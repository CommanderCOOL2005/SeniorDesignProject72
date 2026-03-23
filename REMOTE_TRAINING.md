# Remote 0.5B Model Training Setup (Full ProofWiki)

This setup generates the **entire ProofWiki dataset** on the remote server, so your local machine storage is not used.

## Quick Start (3 Commands)

```bash
# 1. From your Mac, transfer scripts to remote
bash setup_remote_training.sh

# 2. SSH to remote server
ssh omm22003@lean4.cse.uconn.edu

# 3. Run everything: data generation + training (takes ~4-6 hours total)
cd /home/omm22003/distillation
bash train_05b_remote.sh
```

That's it! All data and training happens on the remote server.

---

## What Happens

**Local Machine (Your Mac):**
- Transfers only small script files (Python files, ~50KB total)
- No large files downloaded or stored

**Remote Server (lean4.cse.uconn.edu):**
- Scrapes **all ProofWiki proofs** (~1-2 hours)
- Segments into proof steps
- Builds JSONL training dataset
- Trains 0.5B model with 72B teacher (~2-3 hours)
- Saves final model to disk

**Result:** Full dataset + trained model stored on remote, your Mac stays clean.

---

## Detailed Steps

### Step 1: Local Machine Setup

```bash
cd /Users/omkar/Downloads/CSE\ 4940/Distillation
bash setup_remote_training.sh
```

This transfers:
- `Scrape.py` — ProofWiki scraper
- `StepSegmentation.py` — Proof segmenter
- `build_dataset.py` — JSONL builder
- `distill.py` — Training script
- `requirements.txt` — Dependencies

**Time:** ~1 minute

---

### Step 2: Connect to Remote

```bash
ssh omm22003@lean4.cse.uconn.edu
cd /home/omm22003/distillation
```

---

### Step 3: Run Training (Remote Server)

#### Option A: Run Everything at Once (Recommended)

```bash
bash train_05b_remote.sh
```

This script will:
1. Install dependencies
2. Scrape all ProofWiki proofs (1-2 hours)
3. Segment into steps
4. Build JSONL dataset
5. Train 0.5B model (2-3 hours)

**Total time:** 4-6 hours

#### Option B: Separate Data Generation and Training

If you want to generate data first and monitor separately:

```bash
# Step 1: Generate dataset (1-2 hours)
bash generate_dataset_remote.sh

# Step 2: Later, when ready to train
bash train_05b_remote.sh
```

---

### Step 4: Monitor Training (Optional)

While training runs, you can check progress from another terminal:

```bash
ssh omm22003@lean4.cse.uconn.edu
cd /home/omm22003/distillation
tail -f distilled_model_05b/training.log  # if available
```

---

## After Training Complete

The final model will be saved at:
```
/home/omm22003/distillation/distilled_model_05b/final/
```

### Option 1: Keep on Remote Server
Leave it on the remote server and reference it from your web app (if over network).

### Option 2: Pull Back to Local Machine

```bash
# From your Mac
scp -r omm22003@lean4.cse.uconn.edu:/home/omm22003/distillation/distilled_model_05b \
    /Users/omkar/Downloads/CSE\ 4940/Distillation/
```

Then update your web app at `web_app/app.py` to point to the new model if needed.

---

## Training Configuration

The training uses:
- **Teacher:** Qwen/Qwen2.5-72B-Instruct
- **Student:** Qwen/Qwen2.5-0.5B (fresh from Hugging Face)
- **Dataset:** All ProofWiki proofs (thousands of examples)
- **Epochs:** 3
- **Batch Size:** 4
- **Learning Rate:** 2e-4
- **Temperature:** 2.0
- **GPU Memory:** 60GB (adjust if needed)

To customize, edit `train_05b_remote.sh` before running.

---

## Storage Estimates

On the remote server, you'll use:
- `proofwiki_raw.json`: ~500MB-1GB (raw scraped HTML + text)
- `segmented.json`: ~200-400MB (segmented proofs)
- `dataset.jsonl`: ~300-600MB (training examples)
- `distilled_model_05b/`: ~2-3GB (trained LoRA adapters + checkpoints)

**Total:** ~4-6GB remote storage needed

Your local machine: **~50KB** (just the scripts)

---

## Troubleshooting

### Scraping hangs or fails
- ProofWiki might be rate-limiting. The `--delay 0.5` adds a 0.5s pause between requests.
- You can stop and resume; if `proofwiki_raw.json` exists, it won't re-download.
- Check internet connectivity on the remote server.

### Out of memory during training
Adjust in `train_05b_remote.sh`:
```bash
--batch-size 2      # Reduce from 4
--gradient-accumulation 16  # Increase from 8
```

### Training very slow
This is normal for the full ProofWiki dataset. Monitor GPU:
```bash
watch -n 1 'nvidia-smi'  # Check GPU usage
```

### Want to restart training
```bash
rm -rf distilled_model_05b/
bash train_05b_remote.sh
```

---

## Next Steps

1. Run `bash setup_remote_training.sh` on your Mac
2. SSH to remote and run `bash train_05b_remote.sh`
3. Wait 4-6 hours
4. Pull the final model back to local, or keep it on remote
5. Update your web app to use the new 0.5B model

