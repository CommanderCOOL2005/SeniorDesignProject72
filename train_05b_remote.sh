#!/bin/bash
# Remote training script for 0.5B Distilled Model
# Generates full ProofWiki dataset (if needed) then trains
# Run this on lean4.cse.uconn.edu

set -e

cd "$(dirname "$0")"

echo "=== 0.5B Model Training Pipeline (Full ProofWiki) ==="
echo ""

# Step 0: Setup Python environment
echo "Step 0: Setting up Python environment..."
if command -v conda &> /dev/null; then
    # Try to activate conda environment
    eval "$(conda shell.bash hook)"
    conda activate distill 2>/dev/null || conda create -n distill python=3.10 -y
    conda activate distill
    echo "         ✓ Using conda environment 'distill'"
elif [ -d "venv" ]; then
    source venv/bin/activate
    echo "         ✓ Using local venv"
elif [ -d "$HOME/.venv" ]; then
    source "$HOME/.venv/bin/activate"
    echo "         ✓ Using ~/.venv"
else
    # Create a fresh venv
    echo "         - Creating new venv..."
    python3 -m venv venv
    source venv/bin/activate
    echo "         ✓ Created and activated venv"
fi

# Verify Python works
python --version

# Step 1: Install dependencies
echo ""
echo "Step 1: Installing dependencies..."
pip install -q -U -r requirements.txt beautifulsoup4 requests 2>/dev/null || true
# Fix bitsandbytes for CUDA 13.1 compatibility
echo "         - Fixing bitsandbytes for CUDA 13.1..."
pip install -q --no-cache-dir bitsandbytes 2>/dev/null || true
echo "         ✓ Dependencies installed"

# Step 2: Generate dataset if needed
echo ""
echo "Step 2: Checking/generating ProofWiki dataset..."
if [ ! -f "dataset.jsonl" ]; then
    echo "         Generating full ProofWiki dataset..."

    if [ ! -f "proofwiki_raw.json" ]; then
        echo "         - Scraping ProofWiki..."
        python Scrape.py --output proofwiki_raw.json --delay 0.5 --checkpoint-every 200
    fi

    if [ ! -f "segmented.json" ]; then
        echo "         - Segmenting proofs..."
        python StepSegmentation.py --input proofwiki_raw.json --output segmented.json
    fi

    if [ ! -f "dataset.jsonl" ]; then
        echo "         - Building JSONL dataset..."
        python build_dataset.py --segmented segmented.json --output dataset.jsonl
    fi
fi

if [ ! -f "dataset.jsonl" ] || [ ! -s "dataset.jsonl" ]; then
    echo "ERROR: dataset.jsonl is missing or empty after ProofWiki pipeline." >&2
    exit 1
fi

EXAMPLE_COUNT=$(wc -l < dataset.jsonl)
if [ "$EXAMPLE_COUNT" -le 0 ]; then
    echo "ERROR: dataset.jsonl has zero examples." >&2
    exit 1
fi

echo "         ✓ Dataset ready with $EXAMPLE_COUNT training examples"

# Step 3: Train 0.5B model
echo ""
echo "Step 3: Starting model training..."
echo "         Teacher: Qwen/Qwen2.5-72B-Instruct"
echo "         Student: Qwen/Qwen2.5-0.5B"
echo "         Examples: $EXAMPLE_COUNT"
echo ""

# Set environment variables for optimal training
export PYTORCH_ALLOC_CONF=expandable_segments:True
export BNB_CUDA_VERSION=131
export CUDA_LAUNCH_BLOCKING=0

python distill.py \
  --dataset dataset.jsonl \
  --teacher Qwen/Qwen2.5-72B-Instruct \
  --student Qwen/Qwen2.5-0.5B \
  --output-dir ./distilled_model_05b \
  --epochs 3 \
  --batch-size 4 \
  --gradient-accumulation 8 \
  --learning-rate 2e-4 \
  --temperature 2.0 \
  --alpha 0.5 \
  --max-length 512 \
  --device cuda \
  --teacher-gpu-memory 60GiB \
  --teacher-cpu-memory 200GiB \
  --teacher-offload-folder ./teacher_offload

echo ""
echo "=== Training Complete ==="
echo "Final model saved to: ./distilled_model_05b/final/"
echo ""
echo "To pull the model back to your local machine:"
echo "scp -r omm22003@lean4.cse.uconn.edu:/home/omm22003/distillation/distilled_model_05b \\"
echo "    /Users/omkar/Downloads/CSE\\ 4940/Distillation/"
