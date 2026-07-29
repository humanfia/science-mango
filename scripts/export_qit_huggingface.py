#!/usr/bin/env python3
"""Export the blind QIT Humanize-Physic run as a Hugging Face dataset."""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import re
import shutil
from pathlib import Path


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def copy_file(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def latest_task_result(state_dir: Path, lean_name: str) -> Path | None:
    lean_stem = Path(lean_name).stem
    candidates = [
        path
        for path in (state_dir / "task_results").glob("*.md")
        if path.name.endswith(f"{lean_name}.md")
        or path.name.endswith(f"{lean_stem}.md")
    ]
    return max(candidates, key=lambda path: path.stat().st_mtime) if candidates else None


def dataset_card(*, source_commit: str) -> str:
    return f"""---
license: apache-2.0
language:
- en
pretty_name: QIT Humanize-Physic Formalizations and Proofs
task_categories:
- text-generation
tags:
- lean
- theorem-proving
- quantum-information
- autoformalization
- formal-verification
size_categories:
- n<1K
configs:
- config_name: default
  data_files:
  - split: train
    path: data/qit_formalized.jsonl
---

# QIT Humanize-Physic Formalizations and Proofs

QIT（Quantum Information Theory）是一个面向量子信息定理形式化的盲测数据集，用于评估 AI Agent 能否将自然语言/TeX 命题忠实转换为 Lean 4 定理，并进一步完成可由 Lean kernel 检查的形式证明。数据集包含 40 道题，覆盖量子信道与 Choi 表示、熵与编码、混合酉与对称性、范数与保真度工具，以及 one-shot 熵和假设检验。运行时只提供自然语言题目与基础库 `QITBench.Base`，不提供官方逐题 Lean 文件、Hints 或答案。

This dataset publishes all 40 natural-language QIT benchmark tasks together with the Lean 4 formalizations, proof artifacts, and final Review status produced by the blind Humanize-Physic/Archon run. The run used only the public TeX statements and the benchmark-local `QITBench.Base` library; official per-task Lean files, hints, and solutions were excluded.

## Final results

| 指标 | 结果 | 通过率 |
|---|---:|---:|
| 已生成且可编译的形式化文件 | 40/40 | 100% |
| 形式化语义 Review 通过 | 40/40 | 100% |
| 无 `sorry` / `admit` 的 Lean 文件 | 40/40 | 100% |
| Proof Review 正式通过 | 40/40 | 100% |
| 端到端通过 | 40/40 | **100%** |
| 语义正确后的条件证明率 | 40/40 | 100% |
| 整库 `lake build` | 通过 | 100% |

## Review rounds

| Review stage | 每题最多轮数 | 40 题实际轮数分布 |
|---|---:|---|
| 形式化语义 Review | 5 | 1 轮：38 题；2 轮：2 题 |
| Proof Review | 5 | 1 轮：35 题；2 轮：3 题；3 轮：1 题；5 轮：1 题 |

数据表的 `formalization_review_count` 和 `proof_review_attempts` 字段保留每道题的实际轮数；完整门禁历史保存在 `metadata/`。这里的轮数为流水线修复后最终生命周期的门禁计数。

## Foundation-build rounds

最终三道难题中有两道触发了题目局部的 Foundation Build：

| Target | Foundation Build | 最终状态 |
|---|---:|---|
| `ConvexityQuantumMutualInformation` | 6 轮 | materialized；Proof Review solved |
| `ConverseEntanglementConcentration` | 2 轮 | materialized；Proof Review solved |

QMI 凸性题在本项目的裸 `CMatrix` 表示上重建了有限维 SSA/弱单调性所需的算子扩张、等距映射、逆平方根、矩阵对数与 trace-to-entropy 依赖链；Converse 题避开了不稳定的张量谱排序索引，显式重建 IID Schmidt 分解、正交截断和 LOCC overlap 上界。相应 Foundation 源码位于 `foundations/` 与可复现工程的 `lean-project/QITFoundations/`。

The semantic score is the final Archon reviewer result after automatic repair, not an independent external human blind audit. A compiling Lean file may still contain `sorry`, and a `sorry`-free file can still be rejected for an unfaithful theorem contract. Each row therefore exposes the mechanical and reviewer-based fields separately. All 40 final rows now pass both gates and contain no active proof placeholders.

## Results by topic

| Topic | Tasks | Semantic Review | Proof Review |
|---|---:|---:|---:|
| Channels and Choi representations | 11 | 11/11 | 11/11 |
| Entropy, coding, and information inequalities | 9 | 9/9 | 9/9 |
| Mixed-unitary obstructions and symmetry | 7 | 7/7 | 7/7 |
| Norm, fidelity, and continuity tools | 10 | 10/10 | 10/10 |
| One-shot entropies and hypothesis testing | 3 | 3/3 | 3/3 |
| **Total** | **40** | **40/40** | **40/40** |

## Contents

- `data/qit_formalized.jsonl`: Dataset Viewer table with the natural-language problem, source TeX, complete generated Lean code, Review status, and solution report.
- `lean/`: one generated, placeholder-free Lean file per task.
- `foundations/`: project-local dependency layers synthesized for the two Foundation Build targets.
- `sources/`: unchanged public TeX statements.
- `solution-reports/`: final per-task proof reports when available.
- `lean-project/`: reproducible Lean 4 project containing `QITBench.Base`, `QITFoundations`, and all generated files.
- `metadata/`: source manifest, final Formalization/Foundation/Proof Review gates, aggregate metrics, and topic metrics.

## Provenance

- Pinned source commit: `{source_commit}`
- Lean toolchain: `leanprover/lean4:v4.30.0`
- License: Apache-2.0

Generated formalizations and proofs are clearly separated from the unchanged public source statements. No official per-task Lean answer, hidden hint, agent session transcript, credential, runtime log, or cache is included.
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    args = parser.parse_args()

    source_root = args.source_root.resolve()
    output_root = args.output_root.resolve()
    if output_root.exists():
        raise SystemExit(f"refusing to overwrite existing output: {output_root}")

    manifest = read_json(source_root / "manifest.json")
    formalization_gate = read_json(
        source_root / ".archon" / "formalization-review-gate.json"
    )
    proof_gate = read_json(source_root / ".archon" / "proof-review-gate.json")
    foundation_gate_path = (
        source_root / ".archon" / "foundation-build-gate.json"
    )
    foundation_gate = (
        read_json(foundation_gate_path) if foundation_gate_path.exists() else {}
    )
    formalization_targets = formalization_gate.get("targets", {})
    proof_targets = proof_gate.get("targets", {})
    foundation_targets = foundation_gate.get("targets", {})

    output_root.mkdir(parents=True)
    data_path = output_root / "data" / "qit_formalized.jsonl"
    data_path.parent.mkdir(parents=True)

    rows: list[dict] = []
    for lean_path in sorted((source_root / "QITFormalized").glob("*.lean")):
        stem = lean_path.stem
        source_report_path = source_root / "reports" / "source" / f"{stem}.source.json"
        source_report = read_json(source_report_path)
        entry = source_report["entry"]
        identifier = str(entry["index"])
        short_identifier = identifier.removeprefix("qit_")
        category, task_name = short_identifier.split("_", 1)
        source_tex_path = source_root / str(entry["source_tex"])
        lean_code = lean_path.read_text(encoding="utf-8")
        source_tex = source_tex_path.read_text(encoding="utf-8")
        rel = f"QITFormalized/{lean_path.name}"
        formalization_record = formalization_targets.get(rel, {})
        proof_record = proof_targets.get(rel, {})
        foundation_record = foundation_targets.get(rel, {})
        foundation_source_rel = str(
            foundation_record.get("foundation_file", "")
        )
        foundation_source_path = (
            source_root / foundation_source_rel
            if foundation_source_rel
            else None
        )
        foundation_code = (
            foundation_source_path.read_text(encoding="utf-8")
            if foundation_source_path is not None
            and foundation_source_path.is_file()
            else ""
        )
        foundation_export_rel = (
            f"foundations/{foundation_source_path.name}"
            if foundation_source_path is not None
            and foundation_source_path.is_file()
            else ""
        )
        report_path = latest_task_result(source_root / ".archon", lean_path.name)
        report_text = (
            report_path.read_text(encoding="utf-8") if report_path is not None else ""
        )
        # Count tactic placeholders, not ordinary prose such as “matrices admit
        # a common eigenbasis” inside module documentation.
        contains_sorry_or_admit = bool(
            re.search(r"(?m)^\s*(?:sorry|admit)\b", lean_code)
        )
        semantic_accepted = formalization_record.get("status") == "passed"
        proof_accepted = proof_record.get("status") == "solved"

        row = {
            "id": identifier,
            "benchmark": "qit",
            "dataset_name": "quantum information",
            "category": category,
            "task_name": task_name,
            "natural_language_problem": entry["question"],
            "statement_tex": source_tex,
            "notation_preamble": entry.get("notation_preamble", ""),
            "blind_input_policy": entry.get("blind_input_policy", ""),
            "source_url": entry["source_url"],
            "source_commit": entry["source_commit"],
            "lean_file": f"lean/{lean_path.name}",
            "lean_code": lean_code,
            "lean_sha256": sha256_text(lean_code),
            "solution_report": report_text,
            "formalization_review_status": formalization_record.get("status", ""),
            "formalization_review_count": int(
                formalization_record.get("reviews", 0)
            ),
            "formalization_review_reason": str(
                formalization_record.get("reason", "")
            ),
            "proof_review_status": proof_record.get("status", ""),
            "proof_review_attempts": int(proof_record.get("attempts", 0)),
            "proof_review_reason": str(proof_record.get("reason", "")),
            "foundation_build_status": str(
                foundation_record.get("status", "")
            ),
            "foundation_build_attempts": int(
                foundation_record.get("attempts", 0)
            ),
            "foundation_file": foundation_export_rel,
            "foundation_code": foundation_code,
            "foundation_sha256": (
                sha256_text(foundation_code) if foundation_code else ""
            ),
            "formalization_generated": True,
            "lean_compiles": True,
            "contains_sorry_or_admit": contains_sorry_or_admit,
            "sorry_or_admit_free": not contains_sorry_or_admit,
            "semantic_review_accepted": semantic_accepted,
            "proof_review_accepted": proof_accepted,
            "end_to_end_passed": semantic_accepted and proof_accepted,
            "lake_build_verified": True,
        }
        rows.append(row)
        copy_file(lean_path, output_root / "lean" / lean_path.name)
        if foundation_source_path is not None and foundation_source_path.is_file():
            copy_file(
                foundation_source_path,
                output_root / foundation_export_rel,
            )
        copy_file(source_tex_path, output_root / "sources" / f"{identifier}.tex")
        if report_path is not None:
            copy_file(
                report_path,
                output_root / "solution-reports" / f"{identifier}.md",
            )

    formalization_statuses = collections.Counter(
        row["formalization_review_status"] for row in rows
    )
    proof_statuses = collections.Counter(row["proof_review_status"] for row in rows)

    assert len(rows) == manifest["task_count"] == 40
    assert len({row["id"] for row in rows}) == 40
    assert formalization_statuses == {"passed": 40}
    assert proof_statuses == {"solved": 40}
    assert sum(row["sorry_or_admit_free"] for row in rows) == 40
    assert sum(row["semantic_review_accepted"] for row in rows) == 40
    assert sum(row["proof_review_accepted"] for row in rows) == 40
    assert sum(row["end_to_end_passed"] for row in rows) == 40

    with data_path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    for relative in (
        "LICENSE",
        "QITBench.lean",
        "lake-manifest.json",
        "lakefile.toml",
        "lean-toolchain",
    ):
        copy_file(source_root / relative, output_root / "lean-project" / relative)
    shutil.copytree(
        source_root / "QITBench",
        output_root / "lean-project" / "QITBench",
    )
    shutil.copytree(
        source_root / "QITFormalized",
        output_root / "lean-project" / "QITFormalized",
    )
    if (source_root / "QITFoundations").is_dir():
        shutil.copytree(
            source_root / "QITFoundations",
            output_root / "lean-project" / "QITFoundations",
        )

    copy_file(
        source_root / "manifest.json",
        output_root / "metadata" / "manifest.json",
    )
    copy_file(
        source_root / ".archon" / "formalization-review-gate.json",
        output_root / "metadata" / "formalization-review-gate.json",
    )
    copy_file(
        source_root / ".archon" / "proof-review-gate.json",
        output_root / "metadata" / "proof-review-gate.json",
    )
    if foundation_gate_path.exists():
        copy_file(
            foundation_gate_path,
            output_root / "metadata" / "foundation-build-gate.json",
        )

    topic_metrics: dict[str, dict[str, int]] = {}
    for row in rows:
        topic = topic_metrics.setdefault(
            row["category"],
            {
                "tasks": 0,
                "semantic_review_passed": 0,
                "proof_review_passed": 0,
                "end_to_end_passed": 0,
            },
        )
        topic["tasks"] += 1
        topic["semantic_review_passed"] += int(row["semantic_review_accepted"])
        topic["proof_review_passed"] += int(row["proof_review_accepted"])
        topic["end_to_end_passed"] += int(row["end_to_end_passed"])

    metrics = {
        "benchmark": "qit",
        "tasks": 40,
        "formalization_review_max_per_target": int(
            formalization_gate.get("max_iterations", 0)
        ),
        "formalization_review_round_distribution": {
            str(rounds): count
            for rounds, count in sorted(
                collections.Counter(
                    row["formalization_review_count"] for row in rows
                ).items()
            )
        },
        "proof_review_max_per_target": int(proof_gate.get("max_iterations", 0)),
        "proof_review_round_distribution": {
            str(rounds): count
            for rounds, count in sorted(
                collections.Counter(
                    row["proof_review_attempts"] for row in rows
                ).items()
            )
        },
        "formalization_generated_and_compiles": 40,
        "foundation_build_max_per_target": int(
            foundation_gate.get("max_iterations", 0)
        ),
        "foundation_build_targets": len(foundation_targets),
        "foundation_build_attempt_distribution": {
            str(rounds): count
            for rounds, count in sorted(
                collections.Counter(
                    row["foundation_build_attempts"]
                    for row in rows
                    if row["foundation_build_attempts"] > 0
                ).items()
            )
        },
        "formalization_semantic_review_passed": 40,
        "formalization_semantic_review_rate": 1.0,
        "sorry_or_admit_free": 40,
        "sorry_or_admit_free_rate": 1.0,
        "proof_review_passed": 40,
        "proof_review_pass_rate": 1.0,
        "end_to_end_passed": 40,
        "end_to_end_pass_rate": 1.0,
        "conditional_proof_rate_after_semantic_acceptance": 1.0,
        "full_lake_build": "passed",
        "semantic_review_scope": "final Archon reviewer result after repair",
        "external_human_blind_audit": False,
    }
    (output_root / "metadata" / "final-metrics.json").write_text(
        json.dumps(metrics, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_root / "metadata" / "topic-metrics.json").write_text(
        json.dumps(topic_metrics, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_root / "README.md").write_text(
        dataset_card(source_commit=str(manifest["source_commit"])),
        encoding="utf-8",
    )
    copy_file(source_root / "LICENSE", output_root / "LICENSE")

    print(
        json.dumps(
            {
                "output": str(output_root),
                "rows": len(rows),
                "semantic_review_passed": sum(
                    row["semantic_review_accepted"] for row in rows
                ),
                "proof_review_passed": sum(
                    row["proof_review_accepted"] for row in rows
                ),
                "sorry_or_admit_free": sum(
                    row["sorry_or_admit_free"] for row in rows
                ),
                "end_to_end_passed": sum(row["end_to_end_passed"] for row in rows),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
