#!/usr/bin/env python3
"""
Simple web interface for the AI Proof Verifier
- Form to paste axioms (one per line), goal, and steps (one per line, natural language)
- Optional simple markers for box open/close and dependencies
- Runs `run_session` from `SeniorDesignProject72/ai_proof_verifier_full.py`
- Returns verification feedback and a link to the generated Lean skeleton
"""
from flask import Flask, render_template, request, send_file, jsonify, redirect, url_for
import pathlib
import json
import os
import re
import tempfile

# make sure the verifier package is on path
import sys
sys.path.append(str(pathlib.Path(__file__).resolve().parents[1] / "SeniorDesignProject72"))

from ai_proof_verifier_full import run_session

app = Flask(__name__, template_folder="templates", static_folder="static")

# Helpers to transform user input into the verifier spec

def parse_user_steps(text: str):
    """Parse multiline user steps into list of step dicts.
    Support optional dep annotation at end of line:  "(deps: S1,S2)"
    Recognize lines starting with 'Assume' -> box_open True.
    If a line contains 'Thus' or 'Therefore' and we have an open box -> set box_close True for that step.
    """
    steps = []
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    for i, ln in enumerate(lines, start=1):
        sid = f"S{i}"
        # find deps annotation
        deps = []
        m = re.search(r"\(deps:\s*([A-Za-z0-9_,\s]+)\)\s*$", ln, flags=re.I)
        if m:
            deps = [d.strip() for d in m.group(1).split(',') if d.strip()]
            ln = re.sub(r"\(deps:[^)]+\)\s*$", "", ln, flags=re.I).strip()
        box_open = bool(re.match(r"^Assume\b", ln, flags=re.I))
        box_close = bool(re.search(r"\b(Thus|Therefore|Hence|Henceforth)\b", ln, flags=re.I)) and not box_open
        step = {
            "id": sid,
            "nl": ln,
            "rule": "",  # let the NL mapper attempt to pick a rule
            "deps": deps,
            "formal": None,
            "box_open": box_open,
            "box_close": box_close,
            "parser_meta": {}
        }
        steps.append(step)
    return steps


def extract_from_proof(text: str):
    """Given a single natural-language proof text, extract axioms, goal, and steps.
    Heuristics:
      - Lines starting with 'Given:' or 'Axiom:' are axioms.
      - Line starting with 'Goal:' sets the explicit goal.
      - The final line containing 'Thus'/'Therefore' is used as goal if no explicit 'Goal:' provided.
      - Remaining lines are treated as steps (one per line).
    """
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    axioms = []
    goal_line = None
    step_lines = []
    for ln in lines:
        m = re.match(r"^(Given|Axiom)[:\s]+(.+)$", ln, flags=re.I)
        if m:
            axioms.append(m.group(2).strip())
            continue
        m2 = re.match(r"^Goal[:\s]+(.+)$", ln, flags=re.I)
        if m2:
            goal_line = m2.group(1).strip()
            continue
        step_lines.append(ln)

    # If no explicit goal, try to find last 'Thus/Therefore' step
    if not goal_line:
        for ln in reversed(step_lines):
            m = re.search(r"\b(Thus|Therefore|Hence)\b[:\s]*(.+)$", ln, flags=re.I)
            if m:
                goal_line = m.group(2).strip()
                break

    # Build axiom dicts
    axioms_list = [{"id": f"A{i+1}", "nl": a, "formal": a} for i, a in enumerate(axioms)]
    # Build steps using existing parser helper
    steps = parse_user_steps('\n'.join(step_lines))
    return axioms_list, goal_line or "", steps

@app.route("/", methods=["GET"])
def index():
    example = {
        "proof": "Given: P -> Q\nGiven: P\nFrom P and P -> Q infer Q\nThus Q\nGoal: Q"
    }
    return render_template("index.html", example=example)

@app.route("/verify", methods=["POST"])
def verify():
    # HTML form posts as form-encoded; accept either a 'proof' textarea or explicit fields
    proof_text = request.form.get("proof")
    if proof_text:
        axioms, goal_text, steps = extract_from_proof(proof_text)
    else:
        axioms_text = request.form.get("axioms", "").strip()
        goal_text = request.form.get("goal", "").strip()
        steps_text = request.form.get("steps", "").strip()
        axioms = []
        if axioms_text:
            for i, ln in enumerate([l for l in axioms_text.splitlines() if l.strip()], start=1):
                axioms.append({"id": f"A{i}", "nl": ln, "formal": ln})
        steps = parse_user_steps(steps_text)

    # ensure goal fields are strings (verifier expects strings, not None)
    goal_text = goal_text or ""
    spec = {"axioms": axioms, "goal": {"nl": goal_text, "formal": goal_text}, "steps": steps}

    # try to auto-fill simple dependencies by matching known formulas in step NL text
    known = {a['id']: a.get('formal') or a.get('nl') for a in axioms}
    # include previous steps as potential deps (use their NL/formal)
    for s in steps:
        known[s['id']] = s.get('formal') or s.get('nl')
    # heuristic: for steps with empty deps, find known formula texts that appear in the NL
    for s in steps:
        if not s.get('deps'):
            found = []
            # sort by length to prefer longer matches first
            for fid, txt in sorted(known.items(), key=lambda kv: -len(kv[1] or "")):
                if not txt:
                    continue
                try:
                    if txt in s['nl'] and fid not in found and fid != s['id']:
                        found.append(fid)
                except Exception:
                    continue
            if found:
                # cap deps to first 3 matches to avoid noise
                s['deps'] = found[:3]

    # run verifier
    try:
        out = run_session(spec)
    except Exception as e:
        return render_template("result.html", error=str(e), spec=spec, out=None)

    # prepare lean file path returned by run_session
    lean_path = out.get("lean")

    # Try to locate the lean file in a few candidate locations (current cwd, repo root)
    repo_root = pathlib.Path(__file__).resolve().parents[1]
    app_dir = pathlib.Path(__file__).resolve().parent
    candidates = []
    if lean_path:
        if os.path.isabs(lean_path):
            candidates.append(pathlib.Path(lean_path))
        else:
            candidates.append(pathlib.Path(lean_path))
            candidates.append(repo_root / lean_path)
            candidates.append(app_dir / lean_path)

    found = None
    for p in candidates:
        try:
            if p and p.exists():
                found = p.resolve()
                break
        except Exception:
            continue

    lean_exists = bool(found)
    lean_name = None
    if lean_exists:
        # copy to a safe exports folder under the web_app directory so the app can serve it reliably
        exports_dir = app_dir / "exports"
        exports_dir.mkdir(parents=True, exist_ok=True)
        dest_name = f"{found.stem}_{int(found.stat().st_mtime)}{found.suffix}"
        dest_path = exports_dir / dest_name
        try:
            import shutil
            shutil.copy(str(found), str(dest_path))
            lean_name = dest_name
        except Exception:
            # fallback: serve the original absolute path if copy fails
            dest_path = found
            lean_name = found.name

    return render_template("result.html", spec=spec, out=out, lean_exists=lean_exists, lean_name=lean_name)

@app.route("/download_lean")
def download_lean():
    name = request.args.get("name")
    if not name:
        return "Missing file name", 400
    exports_dir = pathlib.Path(__file__).resolve().parent / "exports"
    path = exports_dir / name
    if not path.exists():
        return "Lean file not found", 404
    return send_file(str(path), as_attachment=True)

@app.route("/api/verify", methods=["POST"])
def api_verify():
    data = request.get_json(force=True)
    # accept either a single 'proof' string or structured fields
    if data.get("proof"):
        proof = data.get("proof")
        axioms, goal_text, steps = extract_from_proof(proof)
    else:
        axioms_list = data.get("axioms", [])
        goal_text = data.get("goal")
        steps_list = data.get("steps", [])
        axioms = [{"id": f"A{i+1}", "nl": a, "formal": a} for i, a in enumerate(axioms_list) if a.strip()]
        steps = []
        for i, s in enumerate(steps_list, start=1):
            steps.append({"id": f"S{i}", "nl": s, "rule": "", "deps": [], "formal": None, "box_open": s.strip().lower().startswith("assume"), "box_close": bool(re.search(r"\b(Thus|Therefore|Hence)", s, flags=re.I)), "parser_meta": {}})

    # try simple deps autofill (same heuristic as HTML form)
    known = {a['id']: a.get('formal') or a.get('nl') for a in axioms}
    for s in steps:
        known[s['id']] = s.get('formal') or s.get('nl')
    for s in steps:
        if not s.get('deps'):
            found = []
            for fid, txt in sorted(known.items(), key=lambda kv: -len(kv[1] or "")):
                if not txt:
                    continue
                try:
                    if txt in s['nl'] and fid not in found and fid != s['id']:
                        found.append(fid)
                except Exception:
                    continue
            if found:
                s['deps'] = found[:3]

    # ensure goal fields are strings (verifier expects strings, not None)
    goal_text = goal_text or ""
    spec = {"axioms": axioms, "goal": {"nl": goal_text, "formal": goal_text}, "steps": steps}
    out = run_session(spec)
    return jsonify(out)

if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
