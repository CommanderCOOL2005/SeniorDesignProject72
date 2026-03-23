#!/usr/bin/env python3
"""
Create a minimal test dataset for training.
This generates dummy proof data in JSONL format.
Replace this with real data once the ProofWiki scraper is fixed.
"""

import json
from pathlib import Path

# Minimal test proofs for training
TEST_PROOFS = [
    {
        "statement": "Prove that the sum of two even numbers is even.",
        "steps": [
            "Let a and b be two even numbers.",
            "By definition of even, a = 2m and b = 2n for some integers m and n.",
            "Then a + b = 2m + 2n = 2(m + n).",
            "Since m + n is an integer, a + b is even.",
        ]
    },
    {
        "statement": "Prove that if n is even, then n^2 is even.",
        "steps": [
            "Assume n is even.",
            "Then n = 2k for some integer k.",
            "Thus n^2 = (2k)^2 = 4k^2 = 2(2k^2).",
            "Since 2k^2 is an integer, n^2 is even.",
        ]
    },
    {
        "statement": "Prove that the square of an odd number is odd.",
        "steps": [
            "Let n be an odd number.",
            "Then n = 2k + 1 for some integer k.",
            "So n^2 = (2k + 1)^2 = 4k^2 + 4k + 1 = 2(2k^2 + 2k) + 1.",
            "Thus n^2 is odd.",
        ]
    },
    {
        "statement": "Prove that the product of two odd numbers is odd.",
        "steps": [
            "Let m and n be odd numbers.",
            "Then m = 2a + 1 and n = 2b + 1 for integers a and b.",
            "So mn = (2a + 1)(2b + 1) = 4ab + 2a + 2b + 1 = 2(2ab + a + b) + 1.",
            "Therefore mn is odd.",
        ]
    },
    {
        "statement": "Prove that the sum of an odd and an even number is odd.",
        "steps": [
            "Let m be an odd number and n be an even number.",
            "Then m = 2a + 1 and n = 2b for integers a and b.",
            "So m + n = (2a + 1) + 2b = 2(a + b) + 1.",
            "Since a + b is an integer, m + n is odd.",
        ]
    },
    {
        "statement": "Prove that if a divides b and b divides c, then a divides c.",
        "steps": [
            "Assume a divides b and b divides c.",
            "Then b = ak and c = b*m for some integers k and m.",
            "Substituting, c = (ak)m = a(km).",
            "Since km is an integer, a divides c.",
        ]
    },
    {
        "statement": "Prove that the sum of consecutive integers from 1 to n is n(n+1)/2.",
        "steps": [
            "Let S = 1 + 2 + ... + n.",
            "Write S in reverse: S = n + (n-1) + ... + 1.",
            "Adding: 2S = (n+1) + (n+1) + ... + (n+1) = n(n+1).",
            "Therefore S = n(n+1)/2.",
        ]
    },
    {
        "statement": "Prove that if gcd(a,b) = 1, then gcd(a, bc) = gcd(a, c).",
        "steps": [
            "Let d = gcd(a, bc).",
            "Since gcd(a, b) = 1, any common divisor of a and b is 1.",
            "Any divisor of both a and bc must divide a and c (since it can't divide b).",
            "Thus gcd(a, bc) = gcd(a, c).",
        ]
    },
]

def build_dataset(proofs: list[dict]) -> list[dict]:
    """Convert proofs into training examples."""
    dataset = []
    for proof in proofs:
        statement = proof["statement"]
        steps = proof["steps"]
        
        partial = ""
        for step in steps:
            dataset.append({
                "instruction": "Generate the next step of the proof.",
                "input": f"Theorem:\n{statement}\n\nProof so far:\n{partial}",
                "output": step,
            })
            partial = (partial + " " + step).strip()
    
    return dataset

def main():
    dataset = build_dataset(TEST_PROOFS)
    
    output_path = Path("dataset.jsonl")
    with output_path.open("w", encoding="utf-8") as f:
        for item in dataset:
            f.write(json.dumps(item, ensure_ascii=False) + "\n")
    
    print(f"✓ Created test dataset with {len(dataset)} training examples")
    print(f"  Saved to: {output_path}")
    print("")
    print("This is a minimal test dataset. For production training,")
    print("fix the ProofWiki scraper or use real proof data.")

if __name__ == "__main__":
    main()
