#!/usr/bin/env python3
"""Simple web interface for the distilled 1.5B math-solution generator."""
from flask import Flask, render_template, request, jsonify
import pathlib
import json
import re
import threading
import time

import torch
from peft import PeftModel
from transformers import AutoModelForCausalLM, AutoTokenizer

app = Flask(__name__, template_folder="templates", static_folder="static")

REPO_ROOT = pathlib.Path(__file__).resolve().parents[1]
MODEL_OPTIONS = {
    "distilled_05b": {
        "label": "0.5B Distilled",
        "kind": "lora",
        "adapter_dir": REPO_ROOT / "distilled_model_05b" / "final",
        "fallback_base": "Qwen/Qwen2.5-0.5B",
    },
    "distilled_15b": {
        "label": "1.5B Distilled",
        "kind": "lora",
        "adapter_dir": REPO_ROOT / "distilled_model" / "final",
        "fallback_base": "Qwen/Qwen2.5-1.5B",
    },
    "base_15b": {
        "label": "1.5B Base",
        "kind": "base",
        "model_name": "Qwen/Qwen2.5-1.5B",
        "tokenizer_name": "Qwen/Qwen2.5-1.5B",
    },
}
DEFAULT_MODEL_CHOICE = "distilled_15b"
DEFAULT_COMPARE_MODEL_CHOICE = "base_15b"
MODEL_CACHE = {}
MODEL_LOCK = threading.Lock()
DEFAULT_MAX_NEW_TOKENS = 660
EXAMPLE_PROBLEM = r"Derive $(\frac{1}{1-r})^2 = 1 + 2r + 3r^2 + 4r^3 + \ldots$."


def logic_text_to_latex(text: str) -> str:
    """Convert verifier-style logic text into a MathJax-friendly LaTeX string."""
    if text is None:
        return ""

    latex = str(text).strip()
    if not latex:
        return ""

    latex = latex.translate(str.maketrans({
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "#": r"\#",
        "%": r"\%",
        "&": r"\&",
        "$": r"\$",
    }))

    replacements = (
        ("<->", r"\\leftrightarrow "),
        ("->", r"\\to "),
        ("→", r"\\to "),
        ("¬", r"\\lnot "),
        ("~", r"\\lnot "),
        ("∧", r"\\land "),
        ("∨", r"\\lor "),
        ("⊥", r"\\bot "),
        ("∀", r"\\forall "),
        ("∃", r"\\exists "),
    )
    for source, target in replacements:
        latex = latex.replace(source, target)

    latex = re.sub(r"\s+", " ", latex).strip()
    return latex


def detect_model_device() -> str:
    if torch.cuda.is_available():
        return "cuda"
    if hasattr(torch.backends, "mps") and torch.backends.mps.is_available():
        return "mps"
    return "cpu"


def get_model_dtype(device: str):
    if device == "cpu":
        return torch.float32
    if device == "cuda":
        return torch.bfloat16
    return torch.float16


def normalize_latex_output(text: str) -> str:
    content = (text or "").strip()
    if not content:
        return ""

    content = re.sub(r"^```(?:latex)?\s*", "", content, flags=re.I)
    content = re.sub(r"\s*```$", "", content)
    return content.strip()


def prepare_mathjax_output(text: str) -> str:
    normalized = normalize_latex_output(text)
    if not normalized:
        return "No output generated."

    has_math_delimiters = any(token in normalized for token in (r"\(", r"\)", r"\[", r"\]", "$$", "$"))
    has_math_environment = bool(re.search(r"\\begin\{(?:aligned|align\*?|equation\*?|gather\*?)\}", normalized))

    if has_math_delimiters or has_math_environment:
        return normalized

    math_like_lines = []
    for raw_line in normalized.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if any(token in line for token in ("=", "^", "_", "\\", "->", "→", "≤", "≥")):
            math_like_lines.append(line)

    if math_like_lines and len(math_like_lines) == len([line for line in normalized.splitlines() if line.strip()]):
        body = " \\\\n".join(math_like_lines)
        return "\\[\n\\begin{aligned}\n" + body + "\n\\end{aligned}\n\\]"

    return normalized


def resolve_model_choice(model_choice: str) -> str:
    if model_choice in MODEL_OPTIONS:
        return model_choice
    return DEFAULT_MODEL_CHOICE


def load_model_bundle(model_choice: str):
    selected = resolve_model_choice(model_choice)
    if selected in MODEL_CACHE:
        return MODEL_CACHE[selected]

    with MODEL_LOCK:
        if selected in MODEL_CACHE:
            return MODEL_CACHE[selected]

        spec = MODEL_OPTIONS[selected]
        device = detect_model_device()
        dtype = get_model_dtype(device)

        model_kwargs = {
            "dtype": dtype,
            "trust_remote_code": True,
        }
        if device == "cuda":
            model_kwargs["device_map"] = "auto"

        if spec["kind"] == "lora":
            adapter_dir = spec["adapter_dir"]
            if not adapter_dir.exists():
                raise FileNotFoundError(f"Model directory not found: {adapter_dir}")

            adapter_config_path = adapter_dir / "adapter_config.json"
            base_model_name = spec["fallback_base"]
            if adapter_config_path.exists():
                with adapter_config_path.open("r", encoding="utf-8") as handle:
                    adapter_config = json.load(handle)
                base_model_name = adapter_config.get("base_model_name_or_path", base_model_name)

            tokenizer = AutoTokenizer.from_pretrained(str(adapter_dir), trust_remote_code=True)
            base_model = AutoModelForCausalLM.from_pretrained(base_model_name, **model_kwargs)
            model = PeftModel.from_pretrained(base_model, str(adapter_dir))
        else:
            tokenizer = AutoTokenizer.from_pretrained(spec["tokenizer_name"], trust_remote_code=True)
            model = AutoModelForCausalLM.from_pretrained(spec["model_name"], **model_kwargs)

        if tokenizer.pad_token is None:
            tokenizer.pad_token = tokenizer.eos_token

        model.eval()
        if device != "cuda":
            model = model.to(device)

        bundle = {
            "tokenizer": tokenizer,
            "model": model,
            "device": device,
            "model_choice": selected,
            "model_label": spec["label"],
        }
        MODEL_CACHE[selected] = bundle
        return bundle


def generate_math_solution(problem: str, model_choice: str = DEFAULT_MODEL_CHOICE, max_new_tokens: int = DEFAULT_MAX_NEW_TOKENS):
    started_at = time.perf_counter()
    bundle = load_model_bundle(model_choice)
    tokenizer = bundle["tokenizer"]
    model = bundle["model"]
    device = bundle["device"]

    prompt = f"""You are a rigorous mathematics assistant.

Solve the following math problem.
Return a readable LaTeX-formatted solution.
Use normal prose for explanation.
Wrap only mathematical expressions in LaTeX delimiters such as \\( ... \\) or \\[ ... \\].
Do not wrap the entire response in one math block unless the entire response is mathematics.
Do not include markdown fences.

Problem:
{problem}
"""

    model_device = getattr(model, "device", None)
    if model_device is None:
        model_device = next(model.parameters()).device

    inputs = tokenizer(prompt, return_tensors="pt", padding=True).to(model_device)
    with torch.no_grad():
        outputs = model.generate(
            **inputs,
            max_new_tokens=max_new_tokens,
            do_sample=False,
            repetition_penalty=1.05,
            pad_token_id=tokenizer.eos_token_id,
        )

    generated_text = tokenizer.decode(outputs[0], skip_special_tokens=True)
    response = generated_text[len(prompt):].strip() or generated_text.strip()
    elapsed_seconds = round(time.perf_counter() - started_at, 2)
    return {
        "problem": problem,
        "raw_output": response,
        "rendered_output": prepare_mathjax_output(response),
        "device": device,
        "model_choice": bundle["model_choice"],
        "model_label": bundle["model_label"],
        "generation_seconds": elapsed_seconds,
    }

@app.route("/", methods=["GET"])
def index():
    example = {
        "problem": EXAMPLE_PROBLEM
    }
    return render_template(
        "index.html",
        example=example,
        generated=None,
        compare_results=None,
        generation_error=None,
        problem_text="",
        selected_model=DEFAULT_MODEL_CHOICE,
        selected_compare_model=DEFAULT_COMPARE_MODEL_CHOICE,
        compare_mode=False,
        model_options=MODEL_OPTIONS,
    )


@app.route("/generate", methods=["POST"])
def generate():
    problem_text = request.form.get("problem", "").strip()
    selected_model = resolve_model_choice(request.form.get("model_choice", DEFAULT_MODEL_CHOICE))
    selected_compare_model = resolve_model_choice(request.form.get("compare_model_choice", DEFAULT_COMPARE_MODEL_CHOICE))
    compare_mode = request.form.get("compare_mode") == "on"
    example = {
        "problem": EXAMPLE_PROBLEM
    }

    if not problem_text:
        return render_template(
            "index.html",
            example=example,
            generated=None,
            compare_results=None,
            generation_error="Enter a math problem.",
            problem_text="",
            selected_model=selected_model,
            selected_compare_model=selected_compare_model,
            compare_mode=compare_mode,
            model_options=MODEL_OPTIONS,
        )

    try:
        if compare_mode:
            first = generate_math_solution(problem_text, model_choice=selected_model)
            second = generate_math_solution(problem_text, model_choice=selected_compare_model)
            generated = None
            compare_results = [first, second]
        else:
            generated = generate_math_solution(problem_text, model_choice=selected_model)
            compare_results = None

        return render_template(
            "index.html",
            example=example,
            generated=generated,
            compare_results=compare_results,
            generation_error=None,
            problem_text=problem_text,
            selected_model=selected_model,
            selected_compare_model=selected_compare_model,
            compare_mode=compare_mode,
            model_options=MODEL_OPTIONS,
        )
    except Exception as exc:
        return render_template(
            "index.html",
            example=example,
            generated=None,
            compare_results=None,
            generation_error=str(exc),
            problem_text=problem_text,
            selected_model=selected_model,
            selected_compare_model=selected_compare_model,
            compare_mode=compare_mode,
            model_options=MODEL_OPTIONS,
        )

@app.route("/api/generate", methods=["POST"])
def api_generate():
    data = request.get_json(force=True)
    problem_text = (data.get("problem") or "").strip()
    selected_model = resolve_model_choice(data.get("model_choice", DEFAULT_MODEL_CHOICE))
    selected_compare_model = resolve_model_choice(data.get("compare_model_choice", DEFAULT_COMPARE_MODEL_CHOICE))
    compare_mode = bool(data.get("compare"))
    if not problem_text:
        return jsonify({"error": "Missing problem"}), 400

    try:
        if compare_mode:
            first = generate_math_solution(problem_text, model_choice=selected_model)
            second = generate_math_solution(problem_text, model_choice=selected_compare_model)
            return jsonify({
                "mode": "compare",
                "results": [first, second],
            })

        generated = generate_math_solution(problem_text, model_choice=selected_model)
    except Exception as exc:
        return jsonify({"error": str(exc)}), 500

    generated["mode"] = "single"
    return jsonify(generated)

if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
