"""
Test the distilled model on proof generation tasks.
"""

import argparse
import json
import os
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel


def load_model(model_path: str, device: str = "cuda"):
    """Load the distilled model."""
    print(f"Loading model from {model_path}...")
    
    # Load base model
    base_model_name = "Qwen/Qwen2.5-0.5B"
    adapter_config_path = os.path.join(model_path, "adapter_config.json")
    if os.path.exists(adapter_config_path):
        with open(adapter_config_path, "r") as f:
            adapter_config = json.load(f)
        base_model_name = adapter_config.get("base_model_name_or_path", base_model_name)
    print(f"Using base model: {base_model_name}")
    tokenizer = AutoTokenizer.from_pretrained(model_path)
    
    # Try loading as LoRA model first
    try:
        base_model = AutoModelForCausalLM.from_pretrained(
            base_model_name,
            device_map="auto",
            torch_dtype=torch.bfloat16,
            trust_remote_code=True,
        )
        model = PeftModel.from_pretrained(base_model, model_path)
        print("Loaded LoRA model")
    except:
        # Load as full model
        model = AutoModelForCausalLM.from_pretrained(
            model_path,
            device_map="auto",
            torch_dtype=torch.bfloat16,
            trust_remote_code=True,
        )
        print("Loaded full model")
    
    model.eval()
    return tokenizer, model


def generate_next_step(
    tokenizer,
    model,
    statement: str,
    partial_proof: str,
    max_new_tokens: int = 150,
    temperature: float = 0.3,
    device: str = "cuda"
):
    """Generate the next step in a proof."""
    
    prompt = f"""Generate the next step of the proof.

Theorem:
{statement}

Proof so far:
{partial_proof}"""
    
    model_device = getattr(model, "device", None)
    if model_device is None:
        model_device = next(model.parameters()).device
    inputs = tokenizer(prompt, return_tensors="pt").to(model_device)
    do_sample = temperature > 0
    
    with torch.no_grad():
        outputs = model.generate(
            **inputs,
            max_new_tokens=max_new_tokens,
            temperature=temperature if do_sample else None,
            do_sample=do_sample,
            top_p=0.9,
            repetition_penalty=1.1,
            remove_invalid_values=True,
            renormalize_logits=True,
        )
    
    generated_text = tokenizer.decode(outputs[0], skip_special_tokens=True)
    
    # Extract only the new generated part
    response = generated_text[len(prompt):].strip()
    return response


def main():
    parser = argparse.ArgumentParser(description="Test distilled model")
    parser.add_argument("--model", default="distilled_model_05b/final", help="Path to distilled model")
    parser.add_argument("--statement", help="Theorem statement")
    parser.add_argument("--statement-file", help="File containing theorem statement")
    parser.add_argument("--proof", default="", help="Partial proof")
    parser.add_argument("--proof-file", help="File containing partial proof")
    parser.add_argument("--max-new-tokens", type=int, default=150)
    parser.add_argument("--temperature", type=float, default=0.3)
    parser.add_argument("--device", default="cuda")
    
    args = parser.parse_args()
    
    # Read inputs
    if args.statement_file:
        with open(args.statement_file, 'r') as f:
            statement = f.read().strip()
    elif args.statement:
        statement = args.statement
    else:
        # Default example
        statement = "If n is even, then n^2 is even."
    
    if args.proof_file:
        with open(args.proof_file, 'r') as f:
            partial_proof = f.read().strip()
    else:
        partial_proof = args.proof
    
    # Load model
    tokenizer, model = load_model(args.model, args.device)
    
    # Generate
    print("\n" + "="*60)
    print("THEOREM:")
    print(statement)
    print("\nPROOF SO FAR:")
    print(partial_proof if partial_proof else "(empty)")
    print("\nGENERATED NEXT STEP:")
    print("="*60)
    
    next_step = generate_next_step(
        tokenizer,
        model,
        statement,
        partial_proof,
        args.max_new_tokens,
        args.temperature,
        args.device
    )
    
    print(next_step)
    print("="*60)


if __name__ == "__main__":
    main()
