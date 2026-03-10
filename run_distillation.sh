#!/bin/bash
# Full pipeline for distillation training
#
# Usage:
#   bash run_distillation.sh                     # default: 1.5B student
#   STUDENT=Qwen/Qwen2.5-0.5B bash run_distillation.sh
#
# Adjust TEACHER_GPU_MEM / TEACHER_CPU_MEM to match your server.
# On a 80 GB A100: TEACHER_GPU_MEM=70GiB TEACHER_CPU_MEM=64GiB
# On a CPU-heavy server (256 GB RAM, small GPU): keep defaults below.

set -e

TEACHER="${TEACHER:-Qwen/Qwen2.5-72B-Instruct}"
STUDENT="${STUDENT:-Qwen/Qwen2.5-1.5B}"
OUTPUT_DIR="${OUTPUT_DIR:-./distilled_model}"
TEACHER_GPU_MEM="${TEACHER_GPU_MEM:-10GiB}"
TEACHER_CPU_MEM="${TEACHER_CPU_MEM:-220GiB}"

echo "=== Knowledge Distillation Pipeline ==="
echo "Teacher : $TEACHER"
echo "Student : $STUDENT"
echo "Output  : $OUTPUT_DIR"
echo ""

# Step 1: Generate dataset (if not already done)
if [ ! -f "dataset.jsonl" ]; then
    echo "Step 1: Generating dataset..."

    if [ ! -f "proofwiki_raw.json" ]; then
        echo "  Scraping ProofWiki..."
        python Scrape.py --output proofwiki_raw.json --delay 0.5 --limit 100
    fi

    if [ ! -f "segmented.json" ]; then
        echo "  Segmenting proofs..."
        python StepSegmentation.py --input proofwiki_raw.json --output segmented.json
    fi

    echo "  Building dataset..."
    python build_dataset.py --segmented segmented.json --output dataset.jsonl
    echo "  Dataset created: dataset.jsonl"
else
    echo "Step 1: Dataset already exists (dataset.jsonl)"
fi

echo ""
echo "Step 2: Installing/updating dependencies..."
pip install -q -U -r requirements.txt

echo ""
echo "Step 3: Starting distillation training..."
python distill.py \
    --dataset dataset.jsonl \
    --teacher "$TEACHER" \
    --student "$STUDENT" \
    --output-dir "$OUTPUT_DIR" \
    --epochs 3 \
    --batch-size 1 \
    --gradient-accumulation 16 \
    --learning-rate 2e-4 \
    --temperature 2.0 \
    --alpha 0.5 \
    --max-length 256 \
    --use-lora \
    --device cuda \
    --teacher-gpu-memory "$TEACHER_GPU_MEM" \
    --teacher-cpu-memory "$TEACHER_CPU_MEM"

echo ""
echo "=== Training Complete ==="
echo "Model saved to: $OUTPUT_DIR/final"
echo ""
echo "To test the model, run:"
echo "  python test_distilled_model.py --model $OUTPUT_DIR/final --device cuda"
