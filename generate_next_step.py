import argparse

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig


def load_teacher(model_name: str, device: str, use_4bit: bool):
    tokenizer = AutoTokenizer.from_pretrained(model_name)

    if device == "cuda":
        device_map = {"": 0}
        dtype = torch.bfloat16
    else:
        device_map = "cpu"
        dtype = torch.float32

    if use_4bit:
        bnb_config = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_compute_dtype=torch.bfloat16,
            bnb_4bit_quant_type="nf4",
            bnb_4bit_use_double_quant=True,
        )
        model = AutoModelForCausalLM.from_pretrained(
            model_name,
            device_map=device_map,
            quantization_config=bnb_config,
            dtype=dtype,
        )
    else:
        model = AutoModelForCausalLM.from_pretrained(
            model_name,
            device_map=device_map,
            dtype=dtype,
        )

    return tokenizer, model


def generate_next_step(
    statement: str,
    partial_proof: str,
    tokenizer: AutoTokenizer,
    teacher: AutoModelForCausalLM,
    device: str,
    max_new_tokens: int,
    temperature: float,
):
    prompt = f"""
You are a rigorous undergraduate mathematics professor.

Theorem:
{statement}

Proof so far:
{partial_proof}

Write the next logical step in the proof.
Be precise and concise.
"""

    inputs = tokenizer(prompt, return_tensors="pt").to(device)

    outputs = teacher.generate(
        **inputs,
        max_new_tokens=max_new_tokens,
        temperature=temperature,
        do_sample=True,
    )

    text = tokenizer.decode(outputs[0], skip_special_tokens=True)
    return text[len(prompt) :].strip()


def read_text(value: str | None, file_path: str | None, label: str) -> str:
    if file_path:
        with open(file_path, "r", encoding="utf-8") as handle:
            return handle.read().strip()
    if value:
        return value
    raise SystemExit(f"Missing {label}. Use --{label} or --{label}-file.")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--model",
        default="deepseek-ai/deepseek-coder-33b-instruct",
    )
    parser.add_argument("--statement")
    parser.add_argument("--statement-file")
    parser.add_argument("--proof")
    parser.add_argument("--proof-file")
    parser.add_argument("--max-new-tokens", type=int, default=120)
    parser.add_argument("--temperature", type=float, default=0.3)
    parser.add_argument("--device", default="cuda")
    parser.add_argument("--no-4bit", action="store_true")

    args = parser.parse_args()

    if args.device == "cuda" and not torch.cuda.is_available():
        raise SystemExit("CUDA not available. Use --device cpu instead.")

    statement = read_text(args.statement, args.statement_file, "statement")
    partial_proof = read_text(args.proof, args.proof_file, "proof")

    tokenizer, teacher = load_teacher(
        args.model,
        device=args.device,
        use_4bit=not args.no_4bit,
    )

    next_step = generate_next_step(
        statement,
        partial_proof,
        tokenizer,
        teacher,
        args.device,
        args.max_new_tokens,
        args.temperature,
    )

    print(next_step)


if __name__ == "__main__":
    main()
