#!/usr/bin/env python3
"""Select formalization-ready IChO theory rows, excluding practical papers."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--id", action="append", dest="ids", default=[])
    args = parser.parse_args()

    selected_ids = set(args.ids)
    selected: list[dict] = []
    for line in args.input.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        entry = json.loads(line)
        paper = str(entry.get("paper") or "")
        if not entry.get("formalization_ready") or not paper.startswith("T"):
            continue
        if selected_ids and entry.get("id") not in selected_ids:
            continue
        selected.append(entry)

    missing = selected_ids - {str(entry.get("id")) for entry in selected}
    if missing:
        raise SystemExit("requested theory IDs were not selected: " + ", ".join(sorted(missing)))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "".join(json.dumps(entry, ensure_ascii=False) + "\n" for entry in selected),
        encoding="utf-8",
    )
    print(f"selected {len(selected)} theory target(s) -> {args.output}")


if __name__ == "__main__":
    main()
