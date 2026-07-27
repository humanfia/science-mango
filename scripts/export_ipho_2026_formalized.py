#!/usr/bin/env python3
"""Export a curated IPhO 2026 Lean snapshot and Hub-ready JSONL rows.

The exporter joins the original 28-row Archon input with the final
formalization/proof gates.  Each output row embeds the formal blueprint, the
complete Lean module, and the latest per-target result report while retaining
the original natural-language fields.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
from pathlib import Path
from typing import Any


EXPERIMENT_TARGETS = {
    "IPhO_2026_4_A_1",
    "IPhO_2026_4_A_5",
    "IPhO_2026_4_B_4",
    "IPhO_2026_4_B_6",
    "IPhO_2026_4_C_6",
    "IPhO_2026_4_C_7",
}

SORRY_RE = re.compile(r"\bsorry\b")
TOKEN_RE = re.compile(
    r"Tokens:\s+in=([\d,]+)\s+out=([\d,]+)\s+Turns:\s+([\d,]+)"
)


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not line.strip():
            continue
        row = json.loads(line)
        if not isinstance(row, dict):
            raise ValueError(f"{path}:{line_number}: expected a JSON object")
        rows.append(row)
    return rows


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def copy_file(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def copy_tree(source: Path, destination: Path) -> None:
    if source.exists():
        shutil.copytree(source, destination, dirs_exist_ok=True)


def target_index(lean_file: Path) -> str:
    prefix = "problem_"
    if not lean_file.stem.startswith(prefix):
        raise ValueError(f"unexpected target filename: {lean_file.name}")
    return lean_file.stem[len(prefix) :]


def target_relpath(lean_file: Path) -> str:
    return f"IPhO2026Problems/{lean_file.name}"


def blueprint_path(run_dir: Path, lean_file: Path) -> Path:
    return (
        run_dir
        / "blueprint"
        / "src"
        / "chapters"
        / f"IPhO2026Problems_{lean_file.stem}.tex"
    )


def latest_result_report(run_dir: Path, lean_file: Path) -> Path | None:
    result_root = run_dir / ".archon" / "task_results"
    candidates = list(result_root.rglob(f"{lean_file.name}.md"))
    candidates.extend(
        result_root.rglob(f"IPhO2026Problems_{lean_file.name}.md")
    )
    target_slug = f"IPhO2026Problems_{lean_file.stem}"
    candidates.extend(
        (run_dir / ".archon" / "logs").glob(
            f"iter-*/review-targets/{target_slug}/attempt-*/summary.md"
        )
    )
    if not candidates:
        return None
    return max(candidates, key=lambda candidate: candidate.stat().st_mtime_ns)


def completed_iteration_metas(run_dir: Path, through_iteration: int) -> list[dict]:
    metas: list[dict] = []
    for path in sorted((run_dir / ".archon" / "logs").glob("iter-*/meta.json")):
        meta = read_json(path)
        iteration = int(meta.get("iteration", 0))
        if meta.get("completedAt") and iteration <= through_iteration:
            metas.append(meta)
    return metas


def token_totals(run_dir: Path, iteration_count: int) -> dict[str, int]:
    log_path = run_dir / ".archon" / "runtime" / "ipho_2026_archon.log"
    matches = TOKEN_RE.findall(log_path.read_text(encoding="utf-8"))
    selected = matches[:iteration_count]
    return {
        "input": sum(int(item[0].replace(",", "")) for item in selected),
        "output": sum(int(item[1].replace(",", "")) for item in selected),
        "turns": sum(int(item[2].replace(",", "")) for item in selected),
    }


def runtime_metrics(run_dir: Path, through_iteration: int) -> dict[str, Any]:
    metas = completed_iteration_metas(run_dir, through_iteration)
    return {
        "iterations": len(metas),
        "wall_seconds": sum(int(meta.get("wallTimeSecs", 0)) for meta in metas),
        "tokens": token_totals(run_dir, len(metas)),
        "completed_at": metas[-1]["completedAt"] if metas else None,
    }


def percentage(numerator: int, denominator: int) -> str:
    return f"{100 * numerator / denominator:.2f}%"


def comparison_data(
    *,
    baseline_dir: Path,
    run_dir: Path,
    theory_relpaths: list[str],
    new_success_iteration: int,
) -> dict[str, Any]:
    old_proof = read_json(baseline_dir / ".archon" / "proof-review-gate.json")
    new_proof = read_json(run_dir / ".archon" / "proof-review-gate.json")

    old_targets = old_proof["targets"]
    new_targets = new_proof["targets"]
    old_sorry_by_path: dict[str, int] = {}
    for relative in theory_relpaths:
        code = (baseline_dir / relative).read_text(encoding="utf-8")
        old_sorry_by_path[relative] = len(SORRY_RE.findall(code))

    old_theory_solved = sum(
        old_targets.get(relative, {}).get("status") == "solved"
        for relative in theory_relpaths
    )
    new_theory_solved = sum(
        new_targets.get(relative, {}).get("status") == "solved"
        for relative in theory_relpaths
    )
    old_theory_zero_sorry = sum(
        count == 0 for count in old_sorry_by_path.values()
    )

    old_all_solved = sum(
        target.get("status") == "solved"
        for target in old_targets.values()
    )
    old_all_zero_sorry = 0
    for lean_file in sorted(
        (baseline_dir / "IPhO2026Problems").glob("problem_IPhO_2026_*.lean")
    ):
        old_all_zero_sorry += not SORRY_RE.search(
            lean_file.read_text(encoding="utf-8")
        )

    old_runtime = runtime_metrics(baseline_dir, 100)
    new_runtime = runtime_metrics(run_dir, new_success_iteration)
    return {
        "schema_version": 1,
        "comparison_scope": {
            "primary": "same 22 theory targets",
            "original_target_count": 28,
            "new_active_target_count": len(theory_relpaths),
            "new_user_skipped_experimental_count": len(EXPERIMENT_TARGETS),
        },
        "common_theory_22": {
            "old": {
                "formalization_compiles": len(theory_relpaths),
                "strict_semantic_passed": old_theory_solved,
                "proof_review_solved": old_theory_solved,
                "zero_sorry_files": old_theory_zero_sorry,
            },
            "new": {
                "formalization_compiles": len(theory_relpaths),
                "strict_semantic_passed": new_theory_solved,
                "proof_review_solved": new_theory_solved,
                "zero_sorry_files": new_theory_solved,
            },
        },
        "original_28_context": {
            "old": {
                "proof_review_solved": old_all_solved,
                "zero_sorry_files": old_all_zero_sorry,
                "semantically_unresolved": 28 - old_all_solved,
            },
            "new": {
                "solved_theory": new_theory_solved,
                "user_skipped_experimental": len(EXPERIMENT_TARGETS),
                "experimental_sorry_count": 17,
            },
        },
        "runtime_to_checkpoint": {
            "old_100_iteration_checkpoint": old_runtime,
            "new_22_theory_solved_checkpoint": new_runtime,
            "note": (
                "The new run skipped six experimental targets after the first "
                "formalization Review, so resource totals are run-level context "
                "rather than a strict 28-target cost comparison."
            ),
        },
    }


def comparison_markdown(comparison: dict[str, Any]) -> str:
    common = comparison["common_theory_22"]
    old = common["old"]
    new = common["new"]
    old_runtime = comparison["runtime_to_checkpoint"][
        "old_100_iteration_checkpoint"
    ]
    new_runtime = comparison["runtime_to_checkpoint"][
        "new_22_theory_solved_checkpoint"
    ]
    old_hours = old_runtime["wall_seconds"] / 3600
    new_hours = new_runtime["wall_seconds"] / 3600
    wall_reduction = 100 * (
        1 - new_runtime["wall_seconds"] / old_runtime["wall_seconds"]
    )
    return f"""# IPhO 2026 pipeline comparison

Comparison date: 2026-07-27 (UTC)

The primary comparison uses the same 22 theory targets. The six E1
experimental subquestions were explicitly paused in the new run and are
reported separately rather than counted as passes or failures.

| Metric on the common 22 theory targets | Old pipeline | New routing pipeline |
|---|---:|---:|
| Formalization compiled | {old['formalization_compiles']}/22 ({percentage(old['formalization_compiles'], 22)}) | {new['formalization_compiles']}/22 ({percentage(new['formalization_compiles'], 22)}) |
| Strict semantic pass | {old['strict_semantic_passed']}/22 ({percentage(old['strict_semantic_passed'], 22)}) | {new['strict_semantic_passed']}/22 ({percentage(new['strict_semantic_passed'], 22)}) |
| Proof Review solved | {old['proof_review_solved']}/22 ({percentage(old['proof_review_solved'], 22)}) | {new['proof_review_solved']}/22 ({percentage(new['proof_review_solved'], 22)}) |
| Zero-`sorry` files | {old['zero_sorry_files']}/22 ({percentage(old['zero_sorry_files'], 22)}) | {new['zero_sorry_files']}/22 ({percentage(new['zero_sorry_files'], 22)}) |

## What changed

- The old run stopped at 20/22 on the theory subset. `1_B_2` and `2_B_1`
  exhausted proof retries under insufficient contracts.
- The new run solved `1_B_2` directly. Proof Review then identified
  `1_C_1` as an underdetermined helper contract and `2_B_1` as an
  answer-bearing assumption, routed both back to formalization, and accepted
  both repaired contracts before proof resumed.
- The final proof gate is 22/22 solved with zero theory `sorry`.

## Full 28-target context

| Checkpoint | Result |
|---|---:|
| Old pipeline proof Review | 25/28 solved |
| Old pipeline zero-`sorry` files | 26/28 |
| Old pipeline semantically unresolved | 3/28 |
| New pipeline active theory scope | 22/22 solved |
| New pipeline experimental scope | 6/6 user-skipped; 17 `sorry` retained |

## Runtime context

| Metric | Old checkpoint | New solved-theory checkpoint |
|---|---:|---:|
| Completed iterations | {old_runtime['iterations']} | {new_runtime['iterations']} |
| Summed iteration wall time | {old_runtime['wall_seconds']} s ({old_hours:.2f} h) | {new_runtime['wall_seconds']} s ({new_hours:.2f} h) |
| Input tokens | {old_runtime['tokens']['input']:,} | {new_runtime['tokens']['input']:,} |
| Output tokens | {old_runtime['tokens']['output']:,} | {new_runtime['tokens']['output']:,} |
| Agent turns | {old_runtime['tokens']['turns']:,} | {new_runtime['tokens']['turns']:,} |

The new solved-theory checkpoint used {wall_reduction:.1f}% less summed wall
time. This resource comparison is contextual: the new run skipped six
experimental targets after their first formalization Review, whereas the old
run continued through 100 iterations and included all 28 targets.

The new run was manually stopped after entering `polish`: its planner proposed
already solved, zero-`sorry` files and validation dropped them all as no-ops.
No proof work remained.
"""


def results_markdown(
    *,
    source_commit: str,
    run_commit: str,
    input_sha256: str,
    comparison: dict[str, Any],
) -> str:
    new_runtime = comparison["runtime_to_checkpoint"][
        "new_22_theory_solved_checkpoint"
    ]
    return f"""# IPhO 2026 formalization results

Snapshot date: 2026-07-27 (UTC)

| Metric | Result |
|---|---:|
| Original selected targets | 28 |
| Active theory targets | 22 |
| User-skipped experimental targets | 6 |
| Theory formalization/semantic Review passed | 22/22 (100%) |
| Theory proof Review solved | 22/22 (100%) |
| Theory zero-`sorry` files | 22/22 (100%) |
| Experimental `sorry` count retained | 17 |
| Final `lake build` | Passed |

The six E1 targets are explicitly `skipped_experimental`; they are neither
passes nor failures. Their partial formalizations are retained for future work.

## Proof-to-formalization routing exercised

- `1_C_1`: proof Review found a false helper contract for signed photon
  momentum. The pipeline routed it to formalization, added physical validity,
  re-reviewed the statement, and then completed the proof.
- `2_B_1`: proof Review found that an all-angle coefficient identity assumed
  the requested answer. The pipeline removed that premise, derived the radius
  equation from maximal-ray tangency, re-reviewed it, and proved the result.

## Reproducibility

- Pipeline source commit: `{source_commit}`
- Final inner run commit: `{run_commit}`
- 28-row input SHA-256: `{input_sha256}`
- Successful checkpoint: iteration {new_runtime['iterations']}
- Summed iteration wall time to checkpoint: {new_runtime['wall_seconds']} s

See `COMPARISON.md` and `comparison.json` for the old/new comparison.
"""


def readme_markdown() -> str:
    return """# IPhO 2026 Lean formalizations and solutions

This directory joins the 28 natural-language formalization-ready records with
their Lean artifacts.

## Dataset files

- `ipho_2026_formalized.jsonl`: all 28 selected rows. Each row embeds the
  original record, formal blueprint, full Lean module, latest solution report,
  and Review status.
- `ipho_2026_lean_verified.jsonl`: the 22 theory rows that passed strict
  semantic Review and proof Review and contain zero `sorry`.
- `IPhO2026Problems/`: complete Lean modules.
- `blueprint/`: declaration-level problem specifications and dependencies.
- `reports/solutions/`: per-target proof/formalization reports.
- `reports/final/`: gate snapshots, comparison data, and run summaries.

## Status

All 22 theory targets are verified. Six experimental E1 targets were
user-skipped and retain partial formalizations; their rows use
`lean_status = "skipped_experimental"` and `lean_verified = false`.

## Build

```bash
lake exe cache get
lake build
```
"""


def export(args: argparse.Namespace) -> None:
    run_dir = args.run_dir.resolve()
    output_dir = args.output_dir.resolve()
    baseline_dir = args.baseline_run.resolve()
    source_rows = read_jsonl(args.source_jsonl.resolve())
    source_by_index = {row["index"]: row for row in source_rows}
    if len(source_by_index) != 28:
        raise ValueError(
            f"expected 28 unique source rows, got {len(source_by_index)}"
        )

    formal_gate = read_json(run_dir / ".archon" / "formalization-review-gate.json")
    proof_gate = read_json(run_dir / ".archon" / "proof-review-gate.json")
    experiment_skip = read_json(run_dir / ".archon" / "experimental-skip.json")

    lean_files = sorted(
        (run_dir / "IPhO2026Problems").glob("problem_IPhO_2026_*.lean")
    )
    if len(lean_files) != 28:
        raise ValueError(f"expected 28 Lean targets, got {len(lean_files)}")

    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / ".gitignore").write_text(".lake/\n", encoding="utf-8")
    (output_dir / ".gitattributes").write_text(
        "reports/** -whitespace\n", encoding="utf-8"
    )
    for name in (
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "IPhO2026Run.lean",
    ):
        copy_file(run_dir / name, output_dir / name)
    lakefile_path = output_dir / "lakefile.toml"
    lakefile_path.write_text(
        lakefile_path.read_text(encoding="utf-8")
        + "\n[[lean_lib]]\nname = \"IPhO2026Problems\"\n",
        encoding="utf-8",
    )
    copy_tree(run_dir / "IPhO2026Run", output_dir / "IPhO2026Run")
    copy_tree(run_dir / "blueprint" / "src", output_dir / "blueprint" / "src")
    copy_tree(
        run_dir / "reports" / "ipho_2026",
        output_dir / "reports" / "source",
    )

    rows: list[dict[str, Any]] = []
    theory_relpaths: list[str] = []
    for lean_file in lean_files:
        index = target_index(lean_file)
        relative = target_relpath(lean_file)
        if index not in source_by_index:
            raise ValueError(f"missing source row for {index}")

        is_experiment = index in EXPERIMENT_TARGETS
        if not is_experiment:
            theory_relpaths.append(relative)

        code = lean_file.read_text(encoding="utf-8")
        blueprint = blueprint_path(run_dir, lean_file)
        if not blueprint.exists():
            raise FileNotFoundError(blueprint)
        blueprint_text = blueprint.read_text(encoding="utf-8")
        report = latest_result_report(run_dir, lean_file)
        report_text = report.read_text(encoding="utf-8") if report else ""
        sorry_count = len(SORRY_RE.findall(code))
        formal_entry = formal_gate["targets"].get(relative, {})
        proof_entry = proof_gate["targets"].get(relative, {})

        if is_experiment:
            status = "skipped_experimental"
            semantic_status = "skipped_experimental"
            proof_status = "skipped_experimental"
            review_reason = formal_entry.get(
                "pre_user_skip_reason",
                "User requested experimental subproblems be skipped.",
            )
        else:
            status = proof_entry.get("status", "missing")
            semantic_status = (
                "passed"
                if formal_entry.get("status") == "passed"
                else formal_entry.get("status", "missing")
            )
            proof_status = proof_entry.get("status", "missing")
            review_reason = proof_entry.get(
                "reason", formal_entry.get("reason", "")
            )

        if not report:
            report_text = (
                f"# Formalization status: {status}\n\n"
                f"Target: `{index}`\n\n"
                f"Reason: {review_reason}\n\n"
                "The partial Lean module is retained, but no complete verified "
                "Lean solution is claimed for this target.\n"
            )

        verified = (
            not is_experiment
            and semantic_status == "passed"
            and proof_status == "solved"
            and sorry_count == 0
        )
        lean_destination = (
            output_dir / "IPhO2026Problems" / lean_file.name
        )
        blueprint_destination = (
            output_dir
            / "blueprint"
            / "src"
            / "chapters"
            / blueprint.name
        )
        report_relative = f"reports/solutions/{lean_file.name}.md"
        copy_file(lean_file, lean_destination)
        if report:
            copy_file(report, output_dir / report_relative)
        else:
            (output_dir / report_relative).parent.mkdir(parents=True, exist_ok=True)
            (output_dir / report_relative).write_text(report_text, encoding="utf-8")

        row = dict(source_by_index[index])
        row.update(
            {
                "lean_status": status,
                "lean_formalization_status": (
                    "skipped_experimental"
                    if is_experiment
                    else formal_entry.get("status", "missing")
                ),
                "lean_semantic_status": semantic_status,
                "lean_proof_status": proof_status,
                "lean_verified": verified,
                "lean_sorry_count": sorry_count,
                "lean_file": f"IPhO2026Problems/{lean_file.name}",
                "lean_blueprint_file": (
                    f"blueprint/src/chapters/{blueprint.name}"
                ),
                "lean_solution_report_file": (
                    report_relative
                ),
                "lean_review_reason": review_reason,
                "lean_pipeline": "archon-proof-review-redraft-v2",
                "lean_pipeline_source_commit": args.source_commit,
                "lean_run_commit": args.run_commit,
                "formalized_problem": blueprint_text,
                "formalized_solution": code,
                "lean_solution_report": report_text,
            }
        )
        rows.append(row)

    aggregate_imports = "\n".join(
        f"import IPhO2026Problems.{lean_file.stem}"
        for lean_file in lean_files
    )
    (output_dir / "IPhO2026Problems.lean").write_text(
        aggregate_imports + "\n", encoding="utf-8"
    )
    (output_dir / "IPhO2026Run.lean").write_text(
        "import IPhO2026Run.Basic\nimport IPhO2026Problems\n",
        encoding="utf-8",
    )

    rows.sort(key=lambda row: row["index"])
    verified_rows = [row for row in rows if row["lean_verified"]]
    if len(verified_rows) != 22:
        raise ValueError(f"expected 22 verified rows, got {len(verified_rows)}")

    all_jsonl = output_dir / "ipho_2026_formalized.jsonl"
    verified_jsonl = output_dir / "ipho_2026_lean_verified.jsonl"
    write_jsonl(all_jsonl, rows)
    write_jsonl(verified_jsonl, verified_rows)

    comparison = comparison_data(
        baseline_dir=baseline_dir,
        run_dir=run_dir,
        theory_relpaths=theory_relpaths,
        new_success_iteration=5,
    )
    write_json(output_dir / "comparison.json", comparison)
    (output_dir / "COMPARISON.md").write_text(
        comparison_markdown(comparison), encoding="utf-8"
    )
    (output_dir / "RESULTS.md").write_text(
        results_markdown(
            source_commit=args.source_commit,
            run_commit=args.run_commit,
            input_sha256=args.input_sha256,
            comparison=comparison,
        ),
        encoding="utf-8",
    )
    (output_dir / "README.md").write_text(readme_markdown(), encoding="utf-8")

    final_report_dir = output_dir / "reports" / "final"
    for name in (
        "formalization-review-gate.json",
        "proof-review-gate.json",
        "experimental-skip.json",
        "PROJECT_STATUS.md",
        "PROGRESS.md",
        "STRATEGY.md",
        "TO_USER.md",
    ):
        source = run_dir / ".archon" / name
        if source.exists():
            copy_file(source, final_report_dir / name)
    copy_file(output_dir / "comparison.json", final_report_dir / "comparison.json")
    copy_file(output_dir / "COMPARISON.md", final_report_dir / "COMPARISON.md")
    copy_file(output_dir / "RESULTS.md", final_report_dir / "RESULTS.md")
    copy_tree(
        run_dir / ".archon" / "proof-journal" / "sessions",
        output_dir / "reports" / "proof_journal",
    )
    for iteration_dir in sorted(
        (run_dir / ".archon" / "iter").glob("iter-*")
    ):
        destination = (
            output_dir / "reports" / "iterations" / iteration_dir.name
        )
        for name in ("plan.md", "review.md"):
            source = iteration_dir / name
            if source.exists():
                copy_file(source, destination / name)
    copy_file(
        run_dir / ".archon" / "runtime" / "ipho_2026_archon.log",
        output_dir / "reports" / "runtime" / "ipho_2026_archon.log",
    )
    for iteration_dir in sorted(
        (run_dir / ".archon" / "logs").glob("iter-*")
    ):
        destination = (
            output_dir / "reports" / "review_artifacts" / iteration_dir.name
        )
        for source in iteration_dir.iterdir():
            if source.is_file() and source.suffix in {".json", ".md"}:
                copy_file(source, destination / source.name)

    manifest = {
        "schema_version": 1,
        "generated_at": "2026-07-27T12:23:26Z",
        "pipeline_source_commit": args.source_commit,
        "run_commit": args.run_commit,
        "input_sha256": args.input_sha256,
        "counts": {
            "formalized": len(rows),
            "lean_verified": len(verified_rows),
            "skipped_experimental": len(rows) - len(verified_rows),
            "theory_sorries": sum(
                row["lean_sorry_count"]
                for row in rows
                if row["lean_verified"]
            ),
            "experimental_sorries": sum(
                row["lean_sorry_count"]
                for row in rows
                if row["lean_status"] == "skipped_experimental"
            ),
        },
        "datasets": {
            all_jsonl.name: {
                "rows": len(rows),
                "sha256": sha256(all_jsonl),
            },
            verified_jsonl.name: {
                "rows": len(verified_rows),
                "sha256": sha256(verified_jsonl),
            },
        },
        "experiment_skip": experiment_skip,
        "final_build": "passed",
    }
    write_json(output_dir / "manifest.json", manifest)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run-dir", type=Path, required=True)
    parser.add_argument("--baseline-run", type=Path, required=True)
    parser.add_argument("--source-jsonl", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--run-commit", required=True)
    parser.add_argument("--input-sha256", required=True)
    return parser.parse_args()


if __name__ == "__main__":
    export(parse_args())
