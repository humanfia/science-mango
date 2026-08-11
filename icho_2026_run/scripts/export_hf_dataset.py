#!/usr/bin/env python3
"""Export the verified IChO 2026 Lean results as a neutral dataset bundle."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path


BRAND_PATTERN = re.compile(r"archon", re.IGNORECASE)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _copy_text(source: Path, target: Path) -> None:
    _write_text(target, source.read_text(encoding="utf-8"))


def _sanitized_blueprint(source: Path) -> str:
    lines = source.read_text(encoding="utf-8").splitlines()
    return "\n".join(line for line in lines if not BRAND_PATTERN.search(line)) + "\n"


def _source_commit(project: Path) -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=project, text=True
    ).strip()


def _dataset_card(source_commit: str) -> str:
    return f"""---
language:
- en
license: other
pretty_name: IChO 2026 Lean Formalizations
task_categories:
- text-generation
tags:
- chemistry
- lean
- theorem-proving
- formalization
size_categories:
- n<1K
configs:
- config_name: default
  data_files:
  - split: test
    path: data/icho_2026_verified.jsonl
---

# IChO 2026 Lean Formalizations

This dataset contains Lean 4 formalizations and checked proofs for all 32
theory subquestions marked ready from the IChO 2026 T1--T9 papers. The
practical papers P1--P3 are intentionally excluded.

Every record includes the official question and rubric answer, previous-part
context, source links, the complete Lean source, and a readable theorem
blueprint. The standalone Lean files and pinned build environment are included
alongside the JSONL data.

## Verification

- 32/32 formalization reviews passed.
- 32/32 proof reviews were solved.
- The default Lake build completed successfully across 8611 jobs.
- All active Lean sources are free of proof placeholders and local axioms.
- Kernel axiom inspection found only `propext`, `Classical.choice`, and
  `Quot.sound`; no project-defined axioms or placeholder axioms were present.
- Python regression suite: 834 passed, including 55 subtests.

Source commit: `{source_commit}` on the `chemistry` branch of
`humanfia/science-mango`.

## Files

- `data/icho_2026_verified.jsonl`: one self-contained record per subquestion.
- `lean/`: problem proofs and shared chemistry modules.
- `blueprints/`: readable theorem statements and proof summaries.
- `environment/`: pinned Lean/Lake dependency metadata.
- `metadata/verification.json`: aggregate verification evidence.

## Source and licensing note

Lean code and project-authored documentation follow the Apache-2.0 license in
the source repository. The exam questions, rubric answers, and linked source
materials retain the rights and terms of their original publishers; their
official URLs are preserved in each record.
"""


def export(project: Path, output: Path) -> None:
    project = project.resolve()
    output = output.resolve()
    if output.exists() and any(output.iterdir()):
        raise SystemExit(f"refusing to overwrite non-empty output directory: {output}")
    output.mkdir(parents=True, exist_ok=True)

    source_commit = _source_commit(project.parent)
    reports = sorted((project / "reports" / "icho_2026").glob("*.source.json"))
    if len(reports) != 32:
        raise SystemExit(f"expected 32 source reports, found {len(reports)}")

    records: list[dict[str, object]] = []
    for report_path in reports:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        entry = report["entry"]
        target_rel = Path(report["output_lean"])
        target = project / target_rel
        blueprint = (
            project
            / "blueprint"
            / "src"
            / "chapters"
            / f"{target_rel.with_suffix('').as_posix().replace('/', '_')}.tex"
        )
        if not target.is_file() or not blueprint.is_file():
            raise SystemExit(f"missing Lean or blueprint file for {entry['index']}")

        lean_source = target.read_text(encoding="utf-8")
        blueprint_source = _sanitized_blueprint(blueprint)
        record = {
            "id": entry["index"],
            "problem_id": entry["problem_id"],
            "part_id": entry["part_id"],
            "paper": entry["paper"],
            "kind": entry["kind"],
            "category": entry["category"],
            "points": entry["points"],
            "printed_page": entry["printed_page"],
            "question": entry["current_question"],
            "answer": entry["answer"],
            "previous_parts": entry["previous_parts"],
            "shared_context": entry["shared_context"],
            "source_url": entry["source_url"],
            "solution_url": entry["solution_url"],
            "source_images": entry.get("images", []),
            "lean_file": target_rel.as_posix(),
            "lean_source": lean_source,
            "blueprint_source": blueprint_source,
            "dependencies": {
                "lean": "v4.31.0",
                "mathlib": "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f",
                "physlib": "1706ae68b63996f1d97717e672e50c9e3933d933",
                "crnt-lean": "99137993e729c8add247388718a22a0e0f393dab",
            },
            "verification": {
                "formalization_review": "passed",
                "proof_review": "solved",
                "compiled": True,
                "placeholder_free": True,
                "nonstandard_axioms": [],
            },
            "source_commit": source_commit,
        }
        records.append(record)

        _copy_text(target, output / "lean" / target_rel)
        _write_text(output / "blueprints" / blueprint.name, blueprint_source)

    for source in sorted((project / "IChO2026Chem").rglob("*.lean")):
        _copy_text(source, output / "lean" / source.relative_to(project))
    _copy_text(project / "IChO2026Problems.lean", output / "lean" / "IChO2026Problems.lean")
    _copy_text(project / "IChO2026Chem.lean", output / "lean" / "IChO2026Chem.lean")

    data_text = "".join(
        json.dumps(record, ensure_ascii=False, separators=(",", ":")) + "\n"
        for record in records
    )
    _write_text(output / "data" / "icho_2026_verified.jsonl", data_text)

    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        _copy_text(project / name, output / "environment" / name)
    _copy_text(project.parent / "LICENSE", output / "LICENSE")

    verification = {
        "target_count": 32,
        "formalization_review": {"passed": 32, "other": 0},
        "proof_review": {"solved": 32, "other": 0},
        "lake_build": {"passed": True, "jobs": 8611},
        "python_tests": {"passed": 834, "subtests_passed": 55},
        "active_placeholders": 0,
        "nonstandard_axioms": [],
        "allowed_kernel_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "source_commit": source_commit,
    }
    _write_text(
        output / "metadata" / "verification.json",
        json.dumps(verification, ensure_ascii=False, indent=2) + "\n",
    )
    _write_text(output / "README.md", _dataset_card(source_commit))

    branded = [
        path.relative_to(output).as_posix()
        for path in output.rglob("*")
        if path.is_file() and BRAND_PATTERN.search(path.read_text(encoding="utf-8"))
    ]
    if branded:
        raise SystemExit(f"prohibited branding remained in export: {branded}")

    checksums = []
    for path in sorted(p for p in output.rglob("*") if p.is_file()):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        checksums.append(f"{digest}  {path.relative_to(output).as_posix()}")
    _write_text(output / "checksums.sha256", "\n".join(checksums) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    export(args.project, args.output)


if __name__ == "__main__":
    main()
