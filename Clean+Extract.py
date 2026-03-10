import re
import json

with open("proofwiki_raw.json") as f:
    raw = json.load(f)

structured = []

for item in raw:
    text = item["content"]

    # crude split
    if "Proof." in text:
        parts = text.split("Proof.")
        statement = parts[0]
        proof = parts[1]

        structured.append({
            "title": item["title"],
            "statement": statement.strip(),
            "proof": proof.strip()
        })

with open("proofwiki_structured.json", "w") as f:
    json.dump(structured, f, indent=2)
