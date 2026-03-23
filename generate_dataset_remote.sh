#!/bin/bash
# Remote script to generate FULL ProofWiki dataset
# Run this on the remote server to scrape all proofs and build training dataset
# This can take 1-2 hours depending on ProofWiki size

set -e

echo "=== Generating Full ProofWiki Dataset on Remote Server ==="
cd "$(dirname "$0")"

# Step 0: Setup Python environment
echo "Step 0: Setting up Python environment..."
if command -v conda &> /dev/null; then
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
    echo "         - Creating new venv..."
    python3 -m venv venv
    source venv/bin/activate
    echo "         ✓ Created and activated venv"
fi

python --version

# Step 1: Scrape all proofs from ProofWiki (no limit)
echo ""
echo "Step 1: Scraping ALL proofs from ProofWiki..."
echo "        (This may take 1-2 hours)"
if [ ! -f "proofwiki_raw.json" ]; then
    pip install -q beautifulsoup4 requests tqdm 2>/dev/null || true
    python Scrape.py --output proofwiki_raw.json --delay 0.5
    PROOF_COUNT=$(grep -o '"title"' proofwiki_raw.json | wc -l)
    echo "        ✓ Scraped $PROOF_COUNT proofs"
else
    echo "        ✓ Using existing proofwiki_raw.json"
fi

echo ""
echo "Step 2: Segmenting proofs into steps..."
if [ ! -f "segmented.json" ]; then
    python StepSegmentation.py --input proofwiki_raw.json --output segmented.json
    STATEMENT_COUNT=$(grep -o '"statement"' segmented.json | wc -l)
    echo "        ✓ Segmented into $STATEMENT_COUNT proof statements"
else
    echo "        ✓ Using existing segmented.json"
fi

echo ""
echo "Step 3: Building JSONL training dataset..."
if [ ! -f "dataset.jsonl" ]; then
    python build_dataset.py --segmented segmented.json --output dataset.jsonl
    EXAMPLE_COUNT=$(wc -l < dataset.jsonl)
    echo "        ✓ Built dataset with $EXAMPLE_COUNT training examples"
else
    echo "        ✓ Using existing dataset.jsonl"
fi

echo ""
echo "=== Dataset Generation Complete ==="
echo ""
echo "Dataset Summary:"
ls -lh proofwiki_raw.json segmented.json dataset.jsonl 2>/dev/null | awk '{print "  " $9 ": " $5}'
echo ""
echo "Ready to train! Run: bash train_05b_remote.sh"
echo ""
