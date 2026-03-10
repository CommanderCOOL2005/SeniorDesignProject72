import argparse
import json
import re
from pathlib import Path


def infer_statement_and_proof(text: str) -> tuple[str, str]:
    if "Proof." in text:
        statement, proof = text.split("Proof.", 1)
        return statement.strip(), proof.strip()
    return "", text.strip()


def split_steps(proof_text: str) -> list[str]:
    if not proof_text:
        return []

    lines = [line.strip() for line in proof_text.splitlines() if line.strip()]
    if len(lines) > 1:
        return lines

    sentences = re.split(r"(?<=[.!?])\s+", proof_text.strip())
    return [sentence.strip() for sentence in sentences if sentence.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default="proofwiki_raw.json")
    parser.add_argument("--output", default="segmented.json")
    args = parser.parse_args()

    raw = json.loads(Path(args.input).read_text(encoding="utf-8"))
    structured = []

    for item in raw:
        statement = item.get("statement", "").strip()
        proof_text = item.get("proof_text", "").strip()
        proof_steps = [step.strip() for step in item.get("proof_steps", []) if step.strip()]

        if not statement or not proof_text:
            content = item.get("content", "")
            inferred_statement, inferred_proof = infer_statement_and_proof(content)
            if not statement:
                statement = inferred_statement
            if not proof_text:
                proof_text = inferred_proof

        steps = proof_steps or split_steps(proof_text)
        if not statement or not steps:
            continue

        structured.append(
            {
                "url": item.get("url", ""),
                "title": item.get("title", ""),
                "statement": statement,
                "steps": steps,
            }
        )

    Path(args.output).write_text(
        json.dumps(structured, ensure_ascii=False, indent=2), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
