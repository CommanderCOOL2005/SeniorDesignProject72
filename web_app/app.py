#!/usr/bin/env python3
"""Simple web interface for the distilled 1.5B math-solution generator."""
from flask import Flask, render_template, request, jsonify, redirect
import pathlib
import json
import re
import threading
import time
import os
import gc
import urllib.request
import urllib.error

import torch
from peft import PeftModel
from transformers import AutoModelForCausalLM, AutoTokenizer
from werkzeug.serving import make_server

app = Flask(__name__, template_folder="templates", static_folder="static")

if torch.cuda.is_available():
    torch.backends.cuda.matmul.allow_tf32 = True
    torch.backends.cudnn.allow_tf32 = True

DEFAULT_SSL_CERT_PATH = "/root/cert/lean4_cse_uconn_edu.pem"
DEFAULT_SSL_KEY_PATH = "/root/cert/lean4.cse.uconn.edu.key"
VLLM_BASE_URL = os.environ.get("VLLM_BASE_URL", "").rstrip("/")
VLLM_MODEL_NAME = os.environ.get("VLLM_MODEL_NAME", "Qwen/Qwen2.5-1.5B")
VLLM_ACCELERATED_MODELS = {
    item.strip() for item in os.environ.get("VLLM_ACCELERATED_MODELS", "base_15b").split(",") if item.strip()
}
VLLM_DISTILLED_BASE_URL = os.environ.get("VLLM_DISTILLED_BASE_URL", "").rstrip("/")
VLLM_DISTILLED_MODEL_NAME = os.environ.get("VLLM_DISTILLED_MODEL_NAME", "distilled-15b-vllm")
VLLM_BASE05_BASE_URL = os.environ.get("VLLM_BASE05_BASE_URL", "").rstrip("/")
VLLM_BASE05_MODEL_NAME = os.environ.get("VLLM_BASE05_MODEL_NAME", "qwen-0.5b-vllm")
VLLM_DISTILLED05_BASE_URL = os.environ.get("VLLM_DISTILLED05_BASE_URL", "").rstrip("/")
VLLM_DISTILLED05_MODEL_NAME = os.environ.get("VLLM_DISTILLED05_MODEL_NAME", "distilled-05b-vllm")
VLLM_72B_BASE_URL = os.environ.get("VLLM_72B_BASE_URL", "").rstrip("/")
VLLM_72B_MODEL_NAME = os.environ.get("VLLM_72B_MODEL_NAME", "qwen-72b-vllm")

REPO_ROOT = pathlib.Path(__file__).resolve().parents[1]
MODEL_OPTIONS = {
    "distilled_05b": {
        "label": "0.5B Distilled",
        "kind": "lora",
        "adapter_dir": REPO_ROOT / "distilled_model_05b" / "final",
        "fallback_base": "Qwen/Qwen2.5-0.5B",
    },
    "base_05b": {
        "label": "0.5B Base",
        "kind": "base",
        "model_name": "Qwen/Qwen2.5-0.5B",
        "tokenizer_name": "Qwen/Qwen2.5-0.5B",
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
    "base_72b": {
        "label": "72B Base",
        "kind": "base",
        "model_name": "Qwen/Qwen2.5-72B-Instruct",
        "tokenizer_name": "Qwen/Qwen2.5-72B-Instruct",
    },
}


def model_is_available(spec: dict) -> bool:
    if spec.get("kind") == "lora":
        adapter_dir = spec.get("adapter_dir")
        return bool(adapter_dir and pathlib.Path(adapter_dir).exists())
    return True


MODEL_OPTIONS = {k: v for k, v in MODEL_OPTIONS.items() if model_is_available(v)}
if not MODEL_OPTIONS:
    raise RuntimeError("No models are available. Check model paths and configuration.")

DEFAULT_MODEL_CHOICE = next(
    (k for k in ("distilled_15b", "distilled_05b", "base_15b", "base_72b", "base_05b") if k in MODEL_OPTIONS),
    next(iter(MODEL_OPTIONS)),
)
DEFAULT_COMPARE_MODEL_CHOICE = next(
    (k for k in ("base_15b", "base_72b", "base_05b", "distilled_05b") if k in MODEL_OPTIONS and k != DEFAULT_MODEL_CHOICE),
    DEFAULT_MODEL_CHOICE,
)
MODEL_CACHE = {}
MODEL_LOCK = threading.Lock()
DEFAULT_MAX_NEW_TOKENS = int(os.environ.get("DEFAULT_MAX_NEW_TOKENS", "1024"))
MIN_MAX_NEW_TOKENS = int(os.environ.get("MIN_MAX_NEW_TOKENS", "32"))
MAX_MAX_NEW_TOKENS = int(os.environ.get("MAX_MAX_NEW_TOKENS", "2048"))
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


def build_solution_prompt(problem: str) -> str:
    return f"""You are a rigorous mathematics assistant.

Solve exactly the given math problem. Do not give generic advice.
Use the specific symbols and quantities from the problem statement.
Show essential derivation steps, then provide a final result line.
The final result line must start with: Final Answer:
Use concise explanations and avoid repetition.
Return readable LaTeX formatting, wrapping only mathematical expressions in \\( ... \\) or \\[ ... \\].
Do not include markdown fences.

Problem:
{problem}
"""


def ensure_final_answer_line(text: str) -> str:
    content = (text or "").strip()
    if not content:
        return content
    if "Final Answer:" in content:
        return content

    lines = [line.strip() for line in content.splitlines() if line.strip()]
    tail = lines[-1] if lines else content
    return f"{content}\n\nFinal Answer: {tail}"


def parse_max_new_tokens(raw_value) -> int:
    if raw_value is None or str(raw_value).strip() == "":
        return DEFAULT_MAX_NEW_TOKENS

    try:
        value = int(raw_value)
    except (TypeError, ValueError) as exc:
        raise ValueError("Token limit must be an integer.") from exc

    if value < MIN_MAX_NEW_TOKENS or value > MAX_MAX_NEW_TOKENS:
        raise ValueError(
            f"Token limit must be between {MIN_MAX_NEW_TOKENS} and {MAX_MAX_NEW_TOKENS}."
        )
    return value


def load_model_bundle(model_choice: str):
    selected = resolve_model_choice(model_choice)
    if selected in MODEL_CACHE:
        return MODEL_CACHE[selected]

    with MODEL_LOCK:
        if selected in MODEL_CACHE:
            return MODEL_CACHE[selected]

        # Keep only one loaded model bundle to avoid GPU memory fragmentation/offload
        # when users switch between 72B and smaller models.
        if MODEL_CACHE:
            MODEL_CACHE.clear()
            gc.collect()
            if torch.cuda.is_available():
                torch.cuda.empty_cache()

        spec = MODEL_OPTIONS[selected]
        device = detect_model_device()
        dtype = get_model_dtype(device)

        model_kwargs = {
            "torch_dtype": dtype,
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

            tokenizer = AutoTokenizer.from_pretrained(base_model_name, trust_remote_code=True)
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
    selected = resolve_model_choice(model_choice)
    vllm_target = resolve_vllm_target(selected)
    if vllm_target:
        try:
            return generate_math_solution_vllm(
                problem,
                selected,
                max_new_tokens,
                base_url=vllm_target["base_url"],
                served_model_name=vllm_target["model_name"],
            )
        except Exception:
            # Fall back to local HF generation if the vLLM sidecar is unavailable.
            pass

    started_at = time.perf_counter()
    bundle = load_model_bundle(selected)
    tokenizer = bundle["tokenizer"]
    model = bundle["model"]
    device = bundle["device"]

    prompt = build_solution_prompt(problem)

    model_device = getattr(model, "device", None)
    if model_device is None:
        model_device = next(model.parameters()).device

    inputs = tokenizer(prompt, return_tensors="pt").to(model_device)
    with torch.inference_mode():
        outputs = model.generate(
            **inputs,
            max_new_tokens=max_new_tokens,
            do_sample=False,
            repetition_penalty=1.05,
            use_cache=True,
            pad_token_id=tokenizer.eos_token_id,
        )

    generated_text = tokenizer.decode(outputs[0], skip_special_tokens=True)
    response = generated_text[len(prompt):].strip() or generated_text.strip()
    response = ensure_final_answer_line(response)
    elapsed_seconds = round(time.perf_counter() - started_at, 2)
    return {
        "problem": problem,
        "raw_output": response,
        "rendered_output": prepare_mathjax_output(response),
        "device": device,
        "model_choice": bundle["model_choice"],
        "model_label": bundle["model_label"],
        "max_new_tokens": int(max_new_tokens),
        "generation_seconds": elapsed_seconds,
    }


def resolve_vllm_target(model_choice: str):
    if model_choice == "base_72b" and VLLM_72B_BASE_URL:
        return {
            "base_url": VLLM_72B_BASE_URL,
            "model_name": VLLM_72B_MODEL_NAME,
        }

    if model_choice == "distilled_15b" and VLLM_DISTILLED_BASE_URL:
        return {
            "base_url": VLLM_DISTILLED_BASE_URL,
            "model_name": VLLM_DISTILLED_MODEL_NAME,
        }

    if model_choice == "distilled_05b" and VLLM_DISTILLED05_BASE_URL:
        return {
            "base_url": VLLM_DISTILLED05_BASE_URL,
            "model_name": VLLM_DISTILLED05_MODEL_NAME,
        }

    if model_choice == "base_05b" and VLLM_BASE05_BASE_URL:
        return {
            "base_url": VLLM_BASE05_BASE_URL,
            "model_name": VLLM_BASE05_MODEL_NAME,
        }

    if VLLM_BASE_URL and model_choice in VLLM_ACCELERATED_MODELS:
        return {
            "base_url": VLLM_BASE_URL,
            "model_name": VLLM_MODEL_NAME,
        }

    return None


def generate_math_solution_vllm(
    problem: str,
    model_choice: str,
    max_new_tokens: int,
    *,
    base_url: str,
    served_model_name: str,
):
    started_at = time.perf_counter()
    prompt = build_solution_prompt(problem)

    endpoint = f"{base_url}/completions"
    payload = {
        "model": served_model_name,
        "prompt": prompt,
        "temperature": 0,
        "max_tokens": int(max_new_tokens),
        "stream": False,
    }
    request_obj = urllib.request.Request(
        endpoint,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )

    with urllib.request.urlopen(request_obj, timeout=1800) as resp:
        body = json.loads(resp.read().decode("utf-8"))

    content = ""
    choices = body.get("choices") or []
    if choices:
        content = (choices[0].get("text") or "").strip()
    content = ensure_final_answer_line(content)

    elapsed_seconds = round(time.perf_counter() - started_at, 2)
    return {
        "problem": problem,
        "raw_output": content,
        "rendered_output": prepare_mathjax_output(content),
        "device": "cuda",
        "model_choice": model_choice,
        "model_label": MODEL_OPTIONS[model_choice]["label"] + " (vLLM)",
        "max_new_tokens": int(max_new_tokens),
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
        selected_max_new_tokens=DEFAULT_MAX_NEW_TOKENS,
        min_max_new_tokens=MIN_MAX_NEW_TOKENS,
        max_max_new_tokens=MAX_MAX_NEW_TOKENS,
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
    raw_max_new_tokens = request.form.get("max_new_tokens", "")
    example = {
        "problem": EXAMPLE_PROBLEM
    }

    try:
        max_new_tokens = parse_max_new_tokens(raw_max_new_tokens)
    except ValueError as exc:
        return render_template(
            "index.html",
            example=example,
            generated=None,
            compare_results=None,
            generation_error=str(exc),
            problem_text=problem_text,
            selected_max_new_tokens=raw_max_new_tokens or DEFAULT_MAX_NEW_TOKENS,
            min_max_new_tokens=MIN_MAX_NEW_TOKENS,
            max_max_new_tokens=MAX_MAX_NEW_TOKENS,
            selected_model=selected_model,
            selected_compare_model=selected_compare_model,
            compare_mode=compare_mode,
            model_options=MODEL_OPTIONS,
        )

    if not problem_text:
        return render_template(
            "index.html",
            example=example,
            generated=None,
            compare_results=None,
            generation_error="Enter a math problem.",
            problem_text="",
            selected_max_new_tokens=max_new_tokens,
            min_max_new_tokens=MIN_MAX_NEW_TOKENS,
            max_max_new_tokens=MAX_MAX_NEW_TOKENS,
            selected_model=selected_model,
            selected_compare_model=selected_compare_model,
            compare_mode=compare_mode,
            model_options=MODEL_OPTIONS,
        )

    try:
        if compare_mode:
            first = generate_math_solution(problem_text, model_choice=selected_model, max_new_tokens=max_new_tokens)
            second = generate_math_solution(problem_text, model_choice=selected_compare_model, max_new_tokens=max_new_tokens)
            generated = None
            compare_results = [first, second]
        else:
            generated = generate_math_solution(problem_text, model_choice=selected_model, max_new_tokens=max_new_tokens)
            compare_results = None

        return render_template(
            "index.html",
            example=example,
            generated=generated,
            compare_results=compare_results,
            generation_error=None,
            problem_text=problem_text,
            selected_max_new_tokens=max_new_tokens,
            min_max_new_tokens=MIN_MAX_NEW_TOKENS,
            max_max_new_tokens=MAX_MAX_NEW_TOKENS,
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
            selected_max_new_tokens=max_new_tokens,
            min_max_new_tokens=MIN_MAX_NEW_TOKENS,
            max_max_new_tokens=MAX_MAX_NEW_TOKENS,
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
    try:
        max_new_tokens = parse_max_new_tokens(data.get("max_new_tokens"))
    except ValueError as exc:
        return jsonify({"error": str(exc)}), 400

    if not problem_text:
        return jsonify({"error": "Missing problem"}), 400

    try:
        if compare_mode:
            first = generate_math_solution(problem_text, model_choice=selected_model, max_new_tokens=max_new_tokens)
            second = generate_math_solution(problem_text, model_choice=selected_compare_model, max_new_tokens=max_new_tokens)
            return jsonify({
                "mode": "compare",
                "max_new_tokens": max_new_tokens,
                "results": [first, second],
            })

        generated = generate_math_solution(problem_text, model_choice=selected_model, max_new_tokens=max_new_tokens)
    except Exception as exc:
        return jsonify({"error": str(exc)}), 500

    generated["mode"] = "single"
    return jsonify(generated)


def create_https_redirect_app(https_port: int) -> Flask:
    redirect_app = Flask("https_redirect")

    @redirect_app.route("/", defaults={"path": ""})
    @redirect_app.route("/<path:path>")
    def redirect_to_https(path: str):
        host = request.host.split(":", 1)[0]
        https_host = host if https_port == 443 else f"{host}:{https_port}"
        destination = f"https://{https_host}/{path}"
        query = request.query_string.decode("utf-8")
        if query:
            destination = f"{destination}?{query}"
        return redirect(destination, code=301)

    return redirect_app


def maybe_start_http_redirect_server(host: str, http_port: int, https_port: int):
    redirect_enabled = os.environ.get("REDIRECT_HTTP_TO_HTTPS", "1") in {"1", "true", "True"}
    if not redirect_enabled:
        return None

    redirect_app = create_https_redirect_app(https_port)
    redirect_server = make_server(host, http_port, redirect_app)
    thread = threading.Thread(target=redirect_server.serve_forever, daemon=True)
    thread.start()
    return redirect_server

if __name__ == "__main__":
    host = os.environ.get("FLASK_HOST", "0.0.0.0")
    debug = os.environ.get("FLASK_DEBUG", "0") in {"1", "true", "True"}

    use_https = os.environ.get("USE_HTTPS", "1") in {"1", "true", "True"}
    if use_https:
        cert_file = os.environ.get("SSL_CERT_FILE", DEFAULT_SSL_CERT_PATH)
        key_file = os.environ.get("SSL_KEY_FILE", DEFAULT_SSL_KEY_PATH)
        if not os.path.exists(cert_file) or not os.path.exists(key_file):
            raise FileNotFoundError(
                f"HTTPS enabled but certificate files were not found. cert={cert_file}, key={key_file}"
            )

        https_port = int(os.environ.get("HTTPS_PORT", os.environ.get("PORT", "443")))
        http_port = int(os.environ.get("HTTP_PORT", "80"))
        maybe_start_http_redirect_server(host=host, http_port=http_port, https_port=https_port)
        app.run(host=host, port=https_port, debug=debug, ssl_context=(cert_file, key_file))
    else:
        port = int(os.environ.get("PORT", os.environ.get("FLASK_PORT", "5001")))
        app.run(host=host, port=port, debug=debug)
