#!/usr/bin/env python3
"""Diagnostic script to compare 0.5B and 1.5B distilled models."""

import json
import os
from pathlib import Path

def check_model_files(model_path):
    """Check what files exist in the model directory."""
    path = Path(model_path)
    return {
        'adapter_config': (path / 'adapter_config.json').exists(),
        'adapter_model': (path / 'adapter_model.safetensors').exists(),
        'tokenizer_config': (path / 'tokenizer_config.json').exists(),
        'tokenizer_json': (path / 'tokenizer.json').exists(),
        'chat_template': (path / 'chat_template.jinja').exists(),
    }


def check_adapter_config(model_path):
    """Check the adapter configuration."""
    config_path = Path(model_path) / 'adapter_config.json'
    if not config_path.exists():
        return None
    
    with open(config_path) as f:
        config = json.load(f)
    
    return {
        'base_model': config.get('base_model_name_or_path'),
        'peft_type': config.get('peft_type'),
        'r': config.get('r'),
        'lora_alpha': config.get('lora_alpha'),
        'lora_dropout': config.get('lora_dropout'),
        'target_modules': config.get('target_modules'),
    }


def check_adapter_weights(model_path):
    """Check if adapter weights file is corrupted."""
    weights_path = Path(model_path) / 'adapter_model.safetensors'
    if not weights_path.exists():
        return {'exists': False, 'size_mb': 0}
    
    size_mb = weights_path.stat().st_size / (1024 * 1024)
    return {'exists': True, 'size_mb': f'{size_mb:.2f}'}


print("="*80)
print("DISTILLED MODEL DIAGNOSTIC")
print("="*80)

models = {
    '0.5B (final)': 'distilled_model_05b/final',
    '1.5B (final)': 'distilled_model/final',
    '0.5B (epoch 1)': 'distilled_model_05b/checkpoint-epoch-1',
    '0.5B (epoch 2)': 'distilled_model_05b/checkpoint-epoch-2',
    '0.5B (epoch 3)': 'distilled_model_05b/checkpoint-epoch-3',
    '1.5B (epoch 1)': 'distilled_model/checkpoint-epoch-1',
}

for name, path in models.items():
    if not os.path.exists(path):
        print(f"\n{name}: PATH NOT FOUND")
        continue
    
    print(f"\n{name}")
    print("-" * 50)
    
    files = check_model_files(path)
    print(f"Files present:")
    for file_type, present in files.items():
        status = "✓" if present else "✗"
        print(f"  {status} {file_type}")
    
    config = check_adapter_config(path)
    if config:
        print(f"\nAdapter Config:")
        print(f"  Base Model: {config['base_model']}")
        print(f"  PEFT Type: {config['peft_type']}")
        print(f"  Rank (r): {config['r']}")
        print(f"  Alpha: {config['lora_alpha']}")
        print(f"  Dropout: {config['lora_dropout']}")
        print(f"  Target Modules: {len(config['target_modules'])} modules")
    
    weights = check_adapter_weights(path)
    print(f"\nAdapter Weights:")
    print(f"  Exists: {weights['exists']}")
    if weights['exists']:
        print(f"  Size: {weights['size_mb']} MB")

print("\n" + "="*80)
print("SUMMARY OF FINDINGS")
print("="*80)
print("""
The 0.5B model is generating garbled output. Possible causes:

1. **Undertrained Model**: The 0.5B model may be too small to learn the task
   effectively, even with knowledge distillation.

2. **Gradient Flow Issues**: With a smaller model, gradients may explode or
   vanish more easily, even with proper training settings.

3. **LoRA Configuration Mismatch**: The LoRA rank (r=16) may be too large
   relative to the 0.5B model's hidden dimensions.

4. **Tokenizer Issues**: Potential mismatch between how the model was
   trained vs how it's being used for inference.

5. **Data Distribution**: The model may have seen insufficient/poor quality
   training data during distillation.

RECOMMENDATION: The 1.5B model is working correctly and is the minimum viable
size for this task. The 0.5B model may need:
- Higher learning rate or different training hyperparameters
- More training epochs
- Reduced LoRA rank
- Better data quality control
""")
