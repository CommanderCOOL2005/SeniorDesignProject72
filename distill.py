"""
Knowledge Distillation Training Script
Teacher: Qwen2.5-72B-Instruct
Student: Qwen2.5-1.5B base
"""

import argparse
import json
import logging
from pathlib import Path
from typing import Dict, List

import torch
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader
from torch.nn.utils.rnn import pad_sequence
from transformers import (
    AutoModelForCausalLM,
    AutoTokenizer,
    BitsAndBytesConfig,
    get_linear_schedule_with_warmup,
)
from peft import LoraConfig, get_peft_model, prepare_model_for_kbit_training
from tqdm import tqdm

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class ProofDataset(Dataset):
    """Dataset for proof generation tasks."""
    
    def __init__(self, data_path: str, tokenizer, max_length: int = 512):
        self.tokenizer = tokenizer
        self.max_length = max_length
        self.data = self._load_data(data_path)
        self.encoded = self._pretokenize(self.data)
        
    def _load_data(self, path: str) -> List[Dict]:
        data = []
        with open(path, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line:
                    data.append(json.loads(line))
        return data

    def _pretokenize(self, raw_data: List[Dict]) -> List[Dict]:
        encoded_items: List[Dict] = []
        for item in raw_data:
            prompt = f"{item['instruction']}\n\n{item['input']}"
            completion = item['output']
            full_text = f"{prompt}\n\n{completion}"

            full_encoding = self.tokenizer(
                full_text,
                max_length=self.max_length,
                truncation=True,
                padding=False,
            )
            prompt_encoding = self.tokenizer(
                prompt,
                max_length=self.max_length,
                truncation=True,
                padding=False,
            )

            input_ids = full_encoding['input_ids']
            attention_mask = full_encoding['attention_mask']
            prompt_length = min(len(prompt_encoding['input_ids']), len(input_ids))

            labels = list(input_ids)
            for index in range(prompt_length):
                labels[index] = -100

            encoded_items.append(
                {
                    'input_ids': input_ids,
                    'attention_mask': attention_mask,
                    'labels': labels,
                }
            )

        return encoded_items
    
    def __len__(self):
        return len(self.encoded)
    
    def __getitem__(self, idx):
        item = self.encoded[idx]

        return {
            'input_ids': torch.tensor(item['input_ids'], dtype=torch.long),
            'attention_mask': torch.tensor(item['attention_mask'], dtype=torch.long),
            'labels': torch.tensor(item['labels'], dtype=torch.long),
        }


def collate_batch(batch, pad_token_id: int):
    input_ids = [item['input_ids'] for item in batch]
    attention_masks = [item['attention_mask'] for item in batch]
    labels = [item['labels'] for item in batch]

    padded_input_ids = pad_sequence(input_ids, batch_first=True, padding_value=pad_token_id)
    padded_attention_masks = pad_sequence(attention_masks, batch_first=True, padding_value=0)
    padded_labels = pad_sequence(labels, batch_first=True, padding_value=-100)

    return {
        'input_ids': padded_input_ids,
        'attention_mask': padded_attention_masks,
        'labels': padded_labels,
    }


def load_teacher_model(
    model_name: str,
    device: str,
    teacher_gpu_memory: str = "45GiB",
    teacher_cpu_memory: str = "220GiB",
    offload_folder: str = "./teacher_offload",
):
    """Load teacher model with 4-bit quantization for memory efficiency."""
    logger.info(f"Loading teacher model: {model_name}")
    
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
    
    model_kwargs = {
        "device_map": "auto",
        "torch_dtype": torch.bfloat16,
        "trust_remote_code": True,
        "offload_folder": offload_folder,
        "offload_state_dict": True,
        "low_cpu_mem_usage": True,
    }

    if device == "cuda":
        model_kwargs["max_memory"] = {
            0: teacher_gpu_memory,
            "cpu": teacher_cpu_memory,
        }

    Path(offload_folder).mkdir(parents=True, exist_ok=True)

    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        **model_kwargs,
    )
    model.eval()  # Teacher is always in eval mode
    
    return tokenizer, model


def load_student_model(model_name: str, device: str, use_lora: bool = True):
    """Load student model, optionally with LoRA for efficient fine-tuning."""
    logger.info(f"Loading student model: {model_name}")
    
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
    
    if use_lora:
        # Load with 4-bit for LoRA training
        bnb_config = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_compute_dtype=torch.bfloat16,
            bnb_4bit_quant_type="nf4",
            bnb_4bit_use_double_quant=True,
        )
        
        model = AutoModelForCausalLM.from_pretrained(
            model_name,
            quantization_config=bnb_config,
            device_map="auto",
            torch_dtype=torch.bfloat16,
            trust_remote_code=True,
        )
        
        # Prepare for LoRA training
        model = prepare_model_for_kbit_training(model)
        
        # Configure LoRA
        lora_config = LoraConfig(
            r=16,
            lora_alpha=32,
            target_modules=["q_proj", "k_proj", "v_proj", "o_proj", "gate_proj", "up_proj", "down_proj"],
            lora_dropout=0.05,
            bias="none",
            task_type="CAUSAL_LM"
        )
        
        model = get_peft_model(model, lora_config)
        model.print_trainable_parameters()
    else:
        # Full model training
        model = AutoModelForCausalLM.from_pretrained(
            model_name,
            device_map="auto",
            torch_dtype=torch.bfloat16,
            trust_remote_code=True,
        )
    
    return tokenizer, model


def compute_distillation_loss(
    student_logits: torch.Tensor,
    teacher_logits: torch.Tensor,
    labels: torch.Tensor,
    temperature: float = 2.0,
    alpha: float = 0.5
):
    """
    Compute combined distillation loss.
    
    Args:
        student_logits: Logits from student model
        teacher_logits: Logits from teacher model
        labels: Ground truth labels
        temperature: Temperature for softening distributions
        alpha: Balance between distillation loss (alpha) and CE loss (1-alpha)
    """
    # Align vocab dimension if teacher/student tokenizers differ
    if student_logits.size(-1) != teacher_logits.size(-1):
        shared_vocab_size = min(student_logits.size(-1), teacher_logits.size(-1))
        student_logits = student_logits[..., :shared_vocab_size]
        teacher_logits = teacher_logits[..., :shared_vocab_size]

    # Standard cross-entropy loss
    ce_loss = F.cross_entropy(
        student_logits.view(-1, student_logits.size(-1)),
        labels.view(-1),
        ignore_index=-100
    )
    
    # KL divergence loss for distillation
    # Only compute where labels are not masked (-100)
    mask = (labels != -100).unsqueeze(-1)
    
    student_soft = F.log_softmax(student_logits / temperature, dim=-1)
    teacher_soft = F.softmax(teacher_logits / temperature, dim=-1)
    
    # KL divergence
    kl_loss = F.kl_div(
        student_soft,
        teacher_soft,
        reduction='none'
    ).sum(dim=-1)
    
    # Apply mask and average
    kl_loss = (kl_loss * mask.squeeze(-1)).sum() / mask.sum()
    kl_loss = kl_loss * (temperature ** 2)  # Scale by T^2 as per Hinton et al.
    
    # Combined loss
    loss = alpha * kl_loss + (1 - alpha) * ce_loss
    
    return loss, ce_loss, kl_loss


def train_epoch(
    student_model,
    teacher_model,
    dataloader,
    optimizer,
    scheduler,
    device,
    temperature,
    alpha,
    gradient_accumulation_steps=1
):
    """Train for one epoch."""
    student_model.train()
    teacher_model.eval()
    
    total_loss = 0
    total_ce_loss = 0
    total_kl_loss = 0
    
    progress_bar = tqdm(dataloader, desc="Training")
    
    for step, batch in enumerate(progress_bar):
        input_ids = batch['input_ids'].to(device)
        attention_mask = batch['attention_mask'].to(device)
        labels = batch['labels'].to(device)
        
        # Student forward pass
        student_outputs = student_model(
            input_ids=input_ids,
            attention_mask=attention_mask,
            labels=labels
        )
        student_logits = student_outputs.logits
        
        # Teacher forward pass (no gradient)
        with torch.no_grad():
            teacher_outputs = teacher_model(
                input_ids=input_ids,
                attention_mask=attention_mask
            )
            teacher_logits = teacher_outputs.logits
        
        # Compute distillation loss
        loss, ce_loss, kl_loss = compute_distillation_loss(
            student_logits,
            teacher_logits,
            labels,
            temperature,
            alpha
        )
        
        # Normalize loss by accumulation steps
        loss = loss / gradient_accumulation_steps
        loss.backward()
        
        # Update weights
        if (step + 1) % gradient_accumulation_steps == 0:
            torch.nn.utils.clip_grad_norm_(student_model.parameters(), 1.0)
            optimizer.step()
            scheduler.step()
            optimizer.zero_grad()
        
        total_loss += loss.item() * gradient_accumulation_steps
        total_ce_loss += ce_loss.item()
        total_kl_loss += kl_loss.item()
        
        progress_bar.set_postfix({
            'loss': f'{loss.item() * gradient_accumulation_steps:.4f}',
            'ce': f'{ce_loss.item():.4f}',
            'kl': f'{kl_loss.item():.4f}'
        })
    
    avg_loss = total_loss / len(dataloader)
    avg_ce_loss = total_ce_loss / len(dataloader)
    avg_kl_loss = total_kl_loss / len(dataloader)
    
    return avg_loss, avg_ce_loss, avg_kl_loss


def main():
    parser = argparse.ArgumentParser(description="Distillation training")
    parser.add_argument("--dataset", required=True, help="Path to dataset JSONL file")
    parser.add_argument("--teacher", default="Qwen/Qwen2.5-72B-Instruct", help="Teacher model")
    parser.add_argument("--student", default="Qwen/Qwen2.5-1.5B", help="Student model")
    parser.add_argument("--output-dir", default="./distilled_model", help="Output directory")
    parser.add_argument("--epochs", type=int, default=3, help="Number of epochs")
    parser.add_argument("--batch-size", type=int, default=4, help="Batch size")
    parser.add_argument("--gradient-accumulation", type=int, default=4, help="Gradient accumulation steps")
    parser.add_argument("--learning-rate", type=float, default=2e-4, help="Learning rate")
    parser.add_argument("--temperature", type=float, default=2.0, help="Distillation temperature")
    parser.add_argument("--alpha", type=float, default=0.5, help="Distillation loss weight")
    parser.add_argument("--max-length", type=int, default=512, help="Max sequence length")
    parser.add_argument("--use-lora", action="store_true", default=True, help="Use LoRA")
    parser.add_argument("--device", default="cuda", help="Device")
    parser.add_argument("--teacher-gpu-memory", default="45GiB", help="Max GPU memory to allocate for teacher model")
    parser.add_argument("--teacher-cpu-memory", default="220GiB", help="Max CPU RAM for teacher offload")
    parser.add_argument("--teacher-offload-folder", default="./teacher_offload", help="Disk folder for teacher offload")
    parser.add_argument("--num-workers", type=int, default=4, help="DataLoader worker count")
    
    args = parser.parse_args()
    
    # Create output directory
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Load models
    logger.info("Loading models...")
    teacher_tokenizer, teacher_model = load_teacher_model(
        args.teacher,
        args.device,
        teacher_gpu_memory=args.teacher_gpu_memory,
        teacher_cpu_memory=args.teacher_cpu_memory,
        offload_folder=args.teacher_offload_folder,
    )
    student_tokenizer, student_model = load_student_model(args.student, args.device, args.use_lora)
    
    # Use student tokenizer for dataset (should be compatible)
    tokenizer = student_tokenizer
    
    # Load dataset
    logger.info(f"Loading dataset from {args.dataset}")
    dataset = ProofDataset(args.dataset, tokenizer, args.max_length)
    dataloader = DataLoader(
        dataset,
        batch_size=args.batch_size,
        shuffle=True,
        collate_fn=lambda batch: collate_batch(batch, tokenizer.pad_token_id),
        num_workers=args.num_workers,
        pin_memory=(args.device == "cuda"),
    )
    
    logger.info(f"Dataset size: {len(dataset)} examples")
    
    # Setup optimizer and scheduler
    optimizer = torch.optim.AdamW(student_model.parameters(), lr=args.learning_rate)
    
    total_steps = len(dataloader) * args.epochs // args.gradient_accumulation
    scheduler = get_linear_schedule_with_warmup(
        optimizer,
        num_warmup_steps=total_steps // 10,
        num_training_steps=total_steps
    )
    
    # Training loop
    logger.info("Starting training...")
    for epoch in range(args.epochs):
        logger.info(f"\nEpoch {epoch + 1}/{args.epochs}")
        
        avg_loss, avg_ce_loss, avg_kl_loss = train_epoch(
            student_model,
            teacher_model,
            dataloader,
            optimizer,
            scheduler,
            args.device,
            args.temperature,
            args.alpha,
            args.gradient_accumulation
        )
        
        logger.info(f"Epoch {epoch + 1} - Loss: {avg_loss:.4f}, CE: {avg_ce_loss:.4f}, KL: {avg_kl_loss:.4f}")
        
        # Save checkpoint
        checkpoint_dir = output_dir / f"checkpoint-epoch-{epoch + 1}"
        checkpoint_dir.mkdir(exist_ok=True)
        
        if args.use_lora:
            student_model.save_pretrained(checkpoint_dir)
        else:
            student_model.save_pretrained(checkpoint_dir)
        
        tokenizer.save_pretrained(checkpoint_dir)
        logger.info(f"Checkpoint saved to {checkpoint_dir}")
    
    # Save final model
    final_dir = output_dir / "final"
    final_dir.mkdir(exist_ok=True)
    
    if args.use_lora:
        student_model.save_pretrained(final_dir)
    else:
        student_model.save_pretrained(final_dir)
    
    tokenizer.save_pretrained(final_dir)
    logger.info(f"Final model saved to {final_dir}")


if __name__ == "__main__":
    main()
