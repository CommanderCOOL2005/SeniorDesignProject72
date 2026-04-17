# Qwen Proof-Step Distillation

Knowledge distillation pipeline that trains a small Qwen model (1.5B or 0.5B) to generate the next step in a mathematical proof by learning from the Qwen2.5-72B-Instruct teacher. Training data is scraped from [ProofWiki](https://proofwiki.org).

```
Teacher: Qwen/Qwen2.5-72B-Instruct  (provides soft labels)
Student: Qwen/Qwen2.5-1.5B          (learns via LoRA)
Task:    Given a theorem + partial proof, predict the next proof step
```

---

## Hardware Requirements

| Component | Minimum | Recommended |
|-----------|---------|-------------|
| GPU VRAM  | 16 GB (student only + 4-bit) | 40–80 GB A100 |
| CPU RAM   | 64 GB | 220+ GB (for teacher CPU offload) |
| Disk      | 50 GB | 200 GB (teacher weights + offload) |
| OS        | Linux | Linux (CUDA) |

> The 72B teacher is loaded with 4-bit quantization and CPU offload. On a single 80 GB A100, use `--teacher-gpu-memory 70GiB --teacher-cpu-memory 64GiB`. On a CPU-heavy server (e.g. 256 GB RAM, modest GPU), use `--teacher-gpu-memory 10GiB --teacher-cpu-memory 220GiB`.

---

---

## Setup

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
pip install -r requirements.txt
```

> Python 3.10+ required. CUDA 11.8+ required for `bitsandbytes` 4-bit quantization on the teacher.

---

## Full Pipeline

### Step 1 — Scrape ProofWiki

```bash
python Scrape.py --output proofwiki_raw.json --delay 0.5
```

Limit pages while testing:

```bash
python Scrape.py --output proofwiki_raw.json --delay 0.5 --limit 100
```

If you get 0 results from the default category, try:

```bash
python Scrape.py \
  --output proofwiki_raw.json \
  --delay 0.5 \
  --limit 100 \
  --category-url https://proofwiki.org/wiki/Category:Proven_Results
```

### Step 2 — Segment Proofs into Steps

```bash
python StepSegmentation.py --input proofwiki_raw.json --output segmented.json
```

### Step 3 — Build Training Dataset

Creates a JSONL file where each line is one `(theorem, partial_proof) → next_step` example.

```bash
python build_dataset.py --segmented segmented.json --output dataset.jsonl
```

### Step 4 — Run Distillation Training

```bash
python distill.py \
    --dataset dataset.jsonl \
    --teacher Qwen/Qwen2.5-72B-Instruct \
    --student Qwen/Qwen2.5-1.5B \
    --output-dir ./distilled_model \
    --epochs 3 \
    --batch-size 1 \
    --gradient-accumulation 16 \
    --learning-rate 2e-4 \
    --temperature 2.0 \
    --alpha 0.5 \
    --max-length 256 \
    --use-lora \
    --device cuda \
    --teacher-gpu-memory 10GiB \
    --teacher-cpu-memory 220GiB
```

Or run the full pipeline in one command:

```bash
bash run_distillation.sh
```

Checkpoints are saved after each epoch to `distilled_model/checkpoint-epoch-N/`. The final LoRA adapter is written to `distilled_model/final/`.

To distill a smaller 0.5B student instead:

```bash
python distill.py \
    --dataset dataset.jsonl \
    --student Qwen/Qwen2.5-0.5B \
    --output-dir ./distilled_model_05b \
    --epochs 3 \
    --batch-size 1 \
    --gradient-accumulation 16 \
    --learning-rate 2e-4 \
    --max-length 256 \
    --use-lora \
    --device cuda
```

---

## Training Arguments

| Argument | Default | Description |
|----------|---------|-------------|
| `--dataset` | *(required)* | Path to JSONL training file |
| `--teacher` | `Qwen/Qwen2.5-72B-Instruct` | Teacher model (HF Hub ID or local path) |
| `--student` | `Qwen/Qwen2.5-1.5B` | Student model |
| `--output-dir` | `./distilled_model` | Directory for checkpoints and final model |
| `--epochs` | `3` | Training epochs |
| `--batch-size` | `4` | Per-device batch size |
| `--gradient-accumulation` | `4` | Gradient accumulation steps |
| `--learning-rate` | `2e-4` | AdamW learning rate |
| `--temperature` | `2.0` | Distillation temperature (softens teacher logits) |
| `--alpha` | `0.5` | Weight of KL loss; `1-alpha` is CE loss weight |
| `--max-length` | `512` | Maximum sequence length (tokens) |
| `--use-lora` | `True` | Train with LoRA (4-bit quantized student) |
| `--device` | `cuda` | Training device |
| `--teacher-gpu-memory` | `45GiB` | Max GPU VRAM for teacher |
| `--teacher-cpu-memory` | `220GiB` | Max CPU RAM for teacher offload |
| `--teacher-offload-folder` | `./teacher_offload` | Disk folder for teacher offload |

---

## Testing the Distilled Model

```bash
python test_distilled_model.py \
    --model distilled_model/final \
    --statement "The sum of two odd numbers is even." \
    --proof "Assume a and b are odd. Then a = 2m+1 and b = 2n+1 for some integers m, n." \
    --max-new-tokens 80 \
    --device cuda
```

On Apple Silicon (MPS):

```bash
python test_distilled_model.py \
    --model distilled_model/final \
    --statement "The sum of two odd numbers is even." \
    --proof "Assume a and b are odd." \
    --max-new-tokens 80 \
    --temperature 0 \
    --device mps
```

---

## Using the Teacher Directly

If you want to use the full 72B teacher without distillation (requires sufficient RAM):

```bash
python generate_next_step.py \
  --statement "If n is even, then n^2 is even." \
  --proof "Let n be even. Then n = 2k for some integer k."
```

Or read from files:

```bash
python generate_next_step.py \
  --statement-file statement.txt \
  --proof-file proof.txt
```

Options: `--model`, `--device`, `--no-4bit`, `--max-new-tokens`, `--temperature`

---

## Repository Structure

```
distill.py                  # Main distillation training script
generate_next_step.py       # Run the teacher model directly
test_distilled_model.py     # Inference with a distilled LoRA adapter
test_prompt.py              # Quick single-prompt test
Scrape.py                   # Scrape proof pages from ProofWiki
StepSegmentation.py         # Split proofs into individual steps
build_dataset.py            # Build JSONL training dataset
run_distillation.sh         # End-to-end pipeline shell script
requirements.txt
distilled_model/            # Output dir (not committed — see .gitignore)
  checkpoint-epoch-1/
  checkpoint-epoch-2/
  checkpoint-epoch-3/
  final/                    # Final LoRA adapter weights
```

---

## Known Issues

**NaN training loss** — If you see `loss=nan, ce=nan, kl=nan` from the first step, the teacher logits are overflowing during CPU offload. Workarounds:
- Lower `--learning-rate` to `5e-5`
- Reduce `--max-length` to `128`
- Use `--alpha 0.1` to down-weight the KL term
- Add `torch.nan_to_num` guards around `teacher_logits` in `distill.py` before passing to the loss function

**Empty generation output** — A model trained entirely with NaN loss will emit EOS immediately. Verify that at least some training steps show a finite loss before calling the checkpoint usable.

**Empty generation on Apple Silicon (MPS)** — MPS does not support all sampling ops. Use `--temperature 0` (greedy decoding). The test scripts handle this automatically.

---

## Loss Function

The distillation loss combines standard cross-entropy with KL divergence against the teacher's soft targets ([Hinton et al., 2015](https://arxiv.org/abs/1503.02531)):

$$\mathcal{L} = \alpha \cdot T^2 \cdot \text{KL}\!\left(\sigma\!\left(\frac{z_s}{T}\right) \,\|\, \sigma\!\left(\frac{z_t}{T}\right)\right) + (1 - \alpha) \cdot \text{CE}(z_s, y)$$

where $T$ is the distillation temperature, $z_s$ are student logits, $z_t$ are teacher logits, and $y$ are ground-truth labels.

---

## Web App HTTPS Deployment (UConn Network)

The Flask app in [web_app/app.py](web_app/app.py) now supports HTTPS directly and can automatically redirect HTTP traffic to HTTPS.

Certificate defaults (already configured in code):
- Cert: `/root/cert/lean4_cse_uconn_edu.pem`
- Key: `/root/cert/lean4.cse.uconn.edu.key`

Run from the repository root:

```bash
source .venv/bin/activate
export USE_HTTPS=1
export HTTPS_PORT=443
export HTTP_PORT=80
export REDIRECT_HTTP_TO_HTTPS=1
python web_app/app.py
```

Behavior:
- HTTPS served on `0.0.0.0:443` with your certificate/key.
- HTTP listener on `0.0.0.0:80` returns permanent redirects to HTTPS.

Optional environment overrides:
- `SSL_CERT_FILE` and `SSL_KEY_FILE` to use different certificate paths.
- `FLASK_HOST` to change bind host.
- `FLASK_DEBUG=1` for debug mode (not recommended in production).
- `USE_HTTPS=0` to run plain HTTP (`PORT` or `FLASK_PORT`, default `5001`).


