#!/usr/bin/env python3
"""Analyze model architectures and hidden dimensions."""

import torch
from transformers import AutoConfig, AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel

print("="*80)
print("MODEL ARCHITECTURE ANALYSIS")
print("="*80)

models_to_check = [
    ("Qwen2.5-0.5B", "Qwen/Qwen2.5-0.5B"),
    ("Qwen2.5-1.5B", "Qwen/Qwen2.5-1.5B"),
]

for name, model_id in models_to_check:
    print(f"\n{name} ({model_id})")
    print("-" * 50)
    
    try:
        config = AutoConfig.from_pretrained(model_id)
        print(f"Hidden Size: {config.hidden_size}")
        print(f"Intermediate Size: {config.intermediate_size}")
        print(f"Num Attention Heads: {config.num_attention_heads}")
        print(f"Num Hidden Layers: {config.num_hidden_layers}")
        print(f"Vocab Size: {config.vocab_size}")
        
        # Calculate total parameters
        total_params = (
            config.hidden_size * config.vocab_size +  # Embedding
            config.num_hidden_layers * (
                config.hidden_size * config.intermediate_size * 2 +  # FFN
                config.hidden_size * config.hidden_size * 3 +  # QKV projections
                config.hidden_size * config.hidden_size  # Output projection
            )
        )
        print(f"Approx Total Params: {total_params / 1e9:.2f}B")
        
        # Analyze LoRA configuration impact
        lora_r = 16
        lora_alpha = 32
        target_modules_count = 7
        
        # LoRA adds: 2 * hidden_size * r * target_modules per layer
        lora_params_per_layer = 2 * config.hidden_size * lora_r * target_modules_count
        total_lora_params = lora_params_per_layer * config.num_hidden_layers
        
        print(f"\nLoRA Analytics (r=16, α=32):")
        print(f"  LoRA params per layer: {lora_params_per_layer / 1e6:.2f}M")
        print(f"  Total LoRA params: {total_lora_params / 1e6:.2f}M")
        print(f"  LoRA/Model ratio: {total_lora_params / total_params * 100:.2f}%")
        
        # Check if rank is appropriate
        max_rank = min(config.hidden_size // 8, 64)  # Conservative estimate
        print(f"\n  Recommended max rank: {max_rank}")
        if lora_r <= max_rank:
            print(f"  ✓ LoRA rank {lora_r} is reasonable")
        else:
            print(f"  ⚠ LoRA rank {lora_r} may be too high!")
            
    except Exception as e:
        print(f"Error: {e}")

print("\n" + "="*80)
print("LORA RANK ANALYSIS")
print("="*80)
print("""
For LoRA to work effectively:
- Rank should scale with model capability
- For 0.5B models: recommend rank 4-8 (conservative)
- For 1.5B models: rank 16 is acceptable
- For larger models: rank 32+ works well

The 0.5B model with rank=16 may be:
1. Too much capacity for a tiny model to optimize
2. Creating unnecessary parameters that hurt training stability
3. Prone to overfitting given limited parameter budget
""")
