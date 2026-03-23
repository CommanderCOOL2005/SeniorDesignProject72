#!/bin/bash
# Setup script to transfer scripts to remote and generate all ProofWiki data there
# Usage: bash setup_remote_training.sh
# This keeps local storage free - all data generation happens on the remote server

set -e

REMOTE_USER="omm22003"
REMOTE_HOST="lean4.cse.uconn.edu"
REMOTE_PATH="/home/${REMOTE_USER}/distillation"

echo "=== Setting Up Remote 0.5B Model Training ==="
echo ""
echo "This will:"
echo "  1. Transfer scripts to remote server"
echo "  2. Generate FULL ProofWiki dataset on remote (no local storage used)"
echo "  3. Train 0.5B model on remote"
echo ""

# Step 1: Create remote directory
echo "Step 1: Setting up remote directory..."
ssh "${REMOTE_USER}@${REMOTE_HOST}" "mkdir -p ${REMOTE_PATH}"

# Step 2: Transfer scripts to remote (not data!)
echo "Step 2: Transferring scripts and config to remote..."
scp Scrape.py StepSegmentation.py build_dataset.py distill.py requirements.txt \
    train_05b_remote.sh generate_dataset_remote.sh \
    "${REMOTE_USER}@${REMOTE_HOST}:${REMOTE_PATH}/"

echo ""
echo "=== Transfer Complete ==="
echo ""
echo "Next steps (run on remote server):"
echo ""
echo "ssh ${REMOTE_USER}@${REMOTE_HOST}"
echo "cd ${REMOTE_PATH}"
echo ""
echo "# Option 1: Run everything at once (data generation + training)"
echo "bash train_05b_remote.sh"
echo ""
echo "# Option 2: Generate data separately, then train"
echo "bash generate_dataset_remote.sh  # Takes ~1-2 hours for all ProofWiki"
echo "bash train_05b_remote.sh"
echo ""
