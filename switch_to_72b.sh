#!/usr/bin/env bash
set -euo pipefail

ssh -o ControlPath=~/.ssh/cm/%r@%h:%p omm22003@lean4.cse.uconn.edu '
set -e
sudo systemctl stop vllm-qwen15b.service vllm-distilled15b.service vllm-qwen05b.service vllm-distilled05b.service || true
sudo systemctl disable vllm-qwen15b.service vllm-distilled15b.service vllm-qwen05b.service vllm-distilled05b.service || true
sudo systemctl daemon-reload
sudo systemctl enable --now vllm-qwen72b.service
sudo systemctl restart distillation-webapp.service
systemctl is-active vllm-qwen72b.service distillation-webapp.service
'

echo "72B mode enabled (other vLLM services stopped)."
