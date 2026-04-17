#!/usr/bin/env bash
set -euo pipefail

ssh -o ControlPath=~/.ssh/cm/%r@%h:%p omm22003@lean4.cse.uconn.edu '
set -e
sudo systemctl stop vllm-qwen72b.service || true
sudo systemctl disable vllm-qwen72b.service || true
sudo systemctl enable --now vllm-qwen15b.service vllm-distilled15b.service vllm-qwen05b.service vllm-distilled05b.service
sudo systemctl restart distillation-webapp.service
systemctl is-active vllm-qwen15b.service vllm-distilled15b.service vllm-qwen05b.service vllm-distilled05b.service distillation-webapp.service
'

echo "Fast multi-model mode enabled (1.5B/0.5B services running)."
