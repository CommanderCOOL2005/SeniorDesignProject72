#!/usr/bin/env python3
from pathlib import Path
import json

import torch
from peft import PeftModel
from transformers import AutoModelForCausalLM, AutoTokenizer

repo = Path('/home/omm22003/distillation')
adapter_dir = repo / 'distilled_model' / 'final'
out_dir = repo / 'distilled_model_merged_15b_vllm'

cfg = json.loads((adapter_dir / 'adapter_config.json').read_text())
base_model_name = cfg.get('base_model_name_or_path', 'Qwen/Qwen2.5-1.5B')

if out_dir.exists() and (out_dir / 'config.json').exists():
    print('MERGED_EXISTS', out_dir)
    raise SystemExit(0)

print('LOADING_BASE', base_model_name)
base = AutoModelForCausalLM.from_pretrained(
    base_model_name,
    torch_dtype=torch.bfloat16,
    device_map='cpu',
    trust_remote_code=True,
)

print('LOADING_ADAPTER', adapter_dir)
peft_model = PeftModel.from_pretrained(base, str(adapter_dir))

print('MERGING')
merged = peft_model.merge_and_unload()
out_dir.mkdir(parents=True, exist_ok=True)

print('SAVING_MODEL', out_dir)
merged.save_pretrained(str(out_dir), safe_serialization=True)

print('SAVING_TOKENIZER')
tok = AutoTokenizer.from_pretrained(base_model_name, trust_remote_code=True)
tok.save_pretrained(str(out_dir))

print('DONE')
