# SeniorDesignProject72

## Quick Test the Distilled Model

This repository includes a distilled proof-step model adapter at `distilled_model/final`.

### 1) Set up environment

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
pip install torch transformers peft accelerate sentencepiece
```

### 2) Run a smoke test

Run from the repository root:

```bash
python - <<'PY'
import torch
from transformers import AutoTokenizer, AutoModelForCausalLM
from peft import PeftModel

adapter_path = "distilled_model/final"
base_model = "Qwen/Qwen2.5-1.5B"

if torch.cuda.is_available():
	device, dtype = "cuda", torch.bfloat16
elif torch.backends.mps.is_available():
	device, dtype = "mps", torch.float16
else:
	device, dtype = "cpu", torch.float32

tokenizer = AutoTokenizer.from_pretrained(adapter_path)
model_base = AutoModelForCausalLM.from_pretrained(base_model, torch_dtype=dtype)
model = PeftModel.from_pretrained(model_base, adapter_path).to(device).eval()

statement = "If n is even, then n^2 is even."
partial = "Let n be even. Then n = 2k for some integer k."
prompt = f"Generate the next step of the proof.\n\nTheorem:\n{statement}\n\nProof so far:\n{partial}"

inputs = tokenizer(prompt, return_tensors="pt").to(device)
with torch.no_grad():
	out = model.generate(**inputs, max_new_tokens=120, temperature=0.3, do_sample=True, top_p=0.9)

text = tokenizer.decode(out[0], skip_special_tokens=True)
print("\nGenerated next step:\n")
print(text[len(prompt):].strip())
PY
```

If you get a coherent next proof step, the model is set up correctly.

### Notes

- On low-memory machines, use CPU and reduce `max_new_tokens` to 60.
- First run will download the base model from Hugging Face.