import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel

print("Loading distilled model with LoRA adapters...")

# Load the base model first
print("Loading base model (Qwen2.5-0.5B)...")
base_model_path = "Qwen/Qwen2.5-0.5B"
tokenizer = AutoTokenizer.from_pretrained(base_model_path)
model = AutoModelForCausalLM.from_pretrained(
    base_model_path,
    device_map="auto",
    dtype=torch.float16,
)

# Load LoRA adapters
print("Loading LoRA adapters from distilled_model_05b/final...")
model = PeftModel.from_pretrained(model, "distilled_model_05b/final")
model.eval()

# The specific prompt
prompt = "Prove that the sum of two odd numbers is even"

print("\n" + "="*80)
print("PROMPT:")
print("="*80)
print(prompt)
print("="*80)

inputs = tokenizer(prompt, return_tensors="pt").to(model.device)

print("\nGenerating response...")
with torch.no_grad():
    outputs = model.generate(
        **inputs,
        max_length=512,
        num_beams=1,
        temperature=0.7,
        top_p=0.9,
    )

response = tokenizer.decode(outputs[0], skip_special_tokens=True)

print("\n" + "="*80)
print("MODEL RESPONSE:")
print("="*80)
print(response)
print("="*80)
