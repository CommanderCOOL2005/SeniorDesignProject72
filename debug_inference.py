#!/usr/bin/env python3
"""Detailed inference debugging for both models."""

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel

def test_model_inference(model_path, base_model_id):
    """Test model inference step by step."""
    print(f"\nTesting: {model_path}")
    print("-" * 60)
    
    try:
        # Load tokenizer
        print(f"1. Loading tokenizer from {model_path}...")
        tokenizer = AutoTokenizer.from_pretrained(model_path)
        print(f"   ✓ Tokenizer loaded. Vocab size: {len(tokenizer)}")
        
        # Test tokenization
        test_text = "Prove that if a,b are odd"
        tokens = tokenizer(test_text, return_tensors="pt")
        print(f"   ✓ Sample text tokenizes to {len(tokens['input_ids'][0])} tokens")
        
        # Load base model
        print(f"\n2. Loading base model ({base_model_id})...")
        base_model = AutoModelForCausalLM.from_pretrained(
            base_model_id,
            device_map="auto",
            torch_dtype=torch.float16,
        )
        print(f"   ✓ Base model loaded")
        
        # Load LoRA adapters
        print(f"\n3. Loading LoRA adapters from {model_path}...")
        model = PeftModel.from_pretrained(base_model, model_path)
        model.eval()
        print(f"   ✓ LoRA adapters loaded")
        
        # Check if model is merged
        print(f"   - Model is merged: {model.merged}")
        
        # Get model device
        model_device = next(model.parameters()).device
        print(f"   - Model device: {model_device}")
        
        # Test forward pass
        print(f"\n4. Testing forward pass...")
        prompt = "Prove that two odd numbers add to an even number:"
        inputs = tokenizer(prompt, return_tensors="pt").to(model_device)
        
        with torch.no_grad():
            outputs = model.forward(
                input_ids=inputs['input_ids'],
                attention_mask=inputs['attention_mask'],
            )
        
        logits = outputs.logits
        print(f"   ✓ Forward pass successful")
        print(f"   - Output shape: {logits.shape}")
        print(f"   - Last token logits shape: {logits[0, -1].shape}")
        
        # Check for NaN/Inf
        if torch.isnan(logits).any():
            print(f"   ⚠ WARNING: Found NaN in logits!")
        if torch.isinf(logits).any():
            print(f"   ⚠ WARNING: Found Inf in logits!")
        
        # Check logit statistics
        last_token_logits = logits[0, -1]
        print(f"   - Logits min: {last_token_logits.min():.4f}")
        print(f"   - Logits max: {last_token_logits.max():.4f}")
        print(f"   - Logits mean: {last_token_logits.mean():.4f}")
        print(f"   - Logits std: {last_token_logits.std():.4f}")
        
        # Get top-k predictions
        top_k = 5
        top_logits, top_indices = torch.topk(last_token_logits, top_k)
        print(f"\n   Top {top_k} predictions:")
        for i, (logit, idx) in enumerate(zip(top_logits, top_indices)):
            token = tokenizer.decode([idx])
            print(f"     {i+1}. '{token}' (logit: {logit:.4f})")
        
        # Test generation
        print(f"\n5. Testing generation...")
        with torch.no_grad():
            gen_outputs = model.generate(
                **inputs,
                max_new_tokens=20,
                do_sample=False,
                top_k=None,
                top_p=None,
            )
        
        generated_text = tokenizer.decode(gen_outputs[0], skip_special_tokens=False)
        print(f"   ✓ Generation successful")
        print(f"   Generated: {generated_text}")
        
        return True
        
    except Exception as e:
        print(f"   ✗ ERROR: {type(e).__name__}: {e}")
        import traceback
        traceback.print_exc()
        return False


print("="*80)
print("DETAILED INFERENCE DEBUGGING")
print("="*80)

# Test both models
success_05b = test_model_inference("distilled_model_05b/final", "Qwen/Qwen2.5-0.5B")
success_15b = test_model_inference("distilled_model/final", "Qwen/Qwen2.5-1.5B")

print("\n" + "="*80)
print("SUMMARY")
print("="*80)
print(f"0.5B Model: {'✓ PASS' if success_05b else '✗ FAIL'}")
print(f"1.5B Model: {'✓ PASS' if success_15b else '✗ FAIL'}")

if not success_05b and success_15b:
    print("\nThe 0.5B model loading or inference is failing.")
    print("This suggests the LoRA adapters may be corrupted or incompatible.")
