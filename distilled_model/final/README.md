---
base_model: Qwen/Qwen2.5-1.5B
library_name: peft
pipeline_tag: text-generation
tags:
- base_model:adapter:Qwen/Qwen2.5-1.5B
- lora
- transformers
---

# Distillation Proof Helper — Final Adapter Checkpoint

This directory contains the **final LoRA adapter** produced by the distillation pipeline for next-step mathematical proof generation.

## Model Details

- **Base model:** `Qwen/Qwen2.5-1.5B`
- **Adapter type:** LoRA (PEFT)
- **Task:** Generate the next logical proof step from theorem statement + partial proof
- **Training objective:** Distillation from a larger teacher model plus supervised next-token objective
- **Frameworks:** Transformers + PEFT

## What Is Stored Here

This `final/` folder stores adapter and tokenizer assets, including:

- `adapter_model.safetensors`
- `adapter_config.json`
- tokenizer files (`tokenizer.json`, `tokenizer_config.json`)
- chat template metadata

This is **not** a standalone full model checkpoint. Load it together with the base model.

## Quick Start

### Python loading example

```python
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel

adapter_path = "distilled_model/final"
base_model_name = "Qwen/Qwen2.5-1.5B"

tokenizer = AutoTokenizer.from_pretrained(adapter_path)

base_model = AutoModelForCausalLM.from_pretrained(
	base_model_name,
	device_map="auto",
	torch_dtype=torch.bfloat16,
	trust_remote_code=True,
)

model = PeftModel.from_pretrained(base_model, adapter_path)
model.eval()
```

### Generate a next proof step

```python
statement = "If n is even, then n^2 is even."
partial_proof = "Let n be even. Then n = 2k for some integer k."

prompt = f"""Generate the next step of the proof.

Theorem:
{statement}

Proof so far:
{partial_proof}"""

inputs = tokenizer(prompt, return_tensors="pt").to(model.device)
with torch.no_grad():
	outputs = model.generate(
		**inputs,
		max_new_tokens=150,
		temperature=0.3,
		do_sample=True,
		top_p=0.9,
		repetition_penalty=1.1,
	)

generated = tokenizer.decode(outputs[0], skip_special_tokens=True)
next_step = generated[len(prompt):].strip()
print(next_step)
```

### Script-based test

From the project root:

```bash
python test_distilled_model.py --model distilled_model/final
```

## Training Configuration (Project Defaults)

From `distill.py` defaults:

- **Teacher model:** `Qwen/Qwen2.5-72B-Instruct`
- **Student base:** `Qwen/Qwen2.5-1.5B`
- **Epochs:** 3
- **Batch size:** 4
- **Gradient accumulation:** 4
- **Learning rate:** `2e-4`
- **Temperature:** `2.0`
- **Alpha (distillation blend):** `0.5`
- **Max sequence length:** `512`
- **Precision / quantization path:** bfloat16 compute with 4-bit loading in LoRA flow

## Intended Use

- Educational and research workflows for proof-step generation
- Prototyping assistants for undergraduate-level proof writing
- Distillation experiments comparing teacher vs student quality

## Limitations

- Can produce plausible but incorrect proof steps; always verify mathematically
- Performance depends heavily on theorem domain and proof style
- Not intended for high-stakes or unsupervised formal verification
- May inherit errors or biases from source data and teacher outputs

## Safety and Responsible Use

- Keep human review in the loop for all generated proof content
- Treat generated text as a draft, not ground truth
- Do not use outputs as sole evidence for grading or formal correctness claims

## Framework Versions

- PEFT 0.18.1