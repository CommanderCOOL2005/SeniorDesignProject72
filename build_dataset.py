import argparse
import json
from pathlib import Path


def read_segmented(path: Path):
    if path.suffix == ".jsonl":
        items = []
        with path.open("r", encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if not line:
                    continue
                items.append(json.loads(line))
        return items

    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def build_dataset(segmented):
    dataset = []

    for proof in segmented:
        statement = proof["statement"]
        steps = proof["steps"]

        partial = ""
        for step in steps:
            dataset.append(
                {
                    "instruction": "Generate the next step of the proof.",
                    "input": f"Theorem:\n{statement}\n\nProof so far:\n{partial}",
                    "output": step,
                }
            )

            partial = (partial + " " + step).strip()

    return dataset


def write_jsonl(path: Path, items):
    with path.open("w", encoding="utf-8") as handle:
        for item in items:
            handle.write(json.dumps(item, ensure_ascii=False))
            handle.write("\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--segmented", required=True, help="Path to segmented JSON/JSONL")
    parser.add_argument("--output", default="dataset.jsonl")
    args = parser.parse_args()

    segmented = read_segmented(Path(args.segmented))
    dataset = build_dataset(segmented)
    write_jsonl(Path(args.output), dataset)


if __name__ == "__main__":
    main()
