#!/usr/bin/env python3
"""Test the 0.5B distilled model with a specific proof prompt."""

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel

print("Loading distilled 0.5B model with LoRA adapters...")

# Load the base model first
print("Loading base model (Qwen2.5-0.5B)...")
base_model_path = "Qwen/Qwen2.5-0.5B"
tokenizer = AutoTokenizer.from_pretrained(base_model_path)
model = AutoModelForCausalLM.from_pretrained(
    base_model_path,
    device_map="auto",
    torch_dtype=torch.float16,
)

# Load LoRA adapters
print("Loading LoRA adapters from distilled_model_05b/final...")
model = PeftModel.from_pretrained(model, "distilled_model_05b/final")
model.eval()

# The specific proof prompt
proof_prompt = """Prove that if a,b are odd integers, then a + b is an even integer. Start with a = 2k+1 and b = 2m + 1 for some integers k and m."""

print("\n" + "="*80)
print("PROOF PROMPT:")
print("="*80)
print(proof_prompt)
print("="*80)

inputs = tokenizer(proof_prompt, return_tensors="pt").to(model.device)

print("\nGenerating proof...")
with torch.no_grad():
    outputs = model.generate(
        **inputs,
        max_new_tokens=300,
        num_beams=1,
        do_sample=False,
        pad_token_id=tokenizer.eos_token_id,
    )

response = tokenizer.decode(outputs[0], skip_special_tokens=True)

print("\n" + "="*80)
print("MODEL RESPONSE:")
print("="*80)
print(response)
print("="*80)
