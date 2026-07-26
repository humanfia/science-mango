"""Paper-aligned metrics for qcode discovery, MILP, and Lean verification."""

from __future__ import annotations

import argparse
import json
import math
import statistics
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text()) if path.is_file() else {}


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.is_file():
        return []
    rows: list[dict[str, Any]] = []
    for line in path.read_text().splitlines():
        if line.strip():
            rows.append(json.loads(line))
    return rows


def _ratio(numerator: int | float, denominator: int | float) -> float | None:
    return round(float(numerator) / float(denominator), 6) if denominator else None


def _code_key(row: dict[str, Any]) -> tuple[Any, ...] | None:
    try:
        a = row.get("A_terms", row.get("A"))
        b = row.get("B_terms", row.get("B"))
        return (
            int(row["ell"]), int(row["m"]),
            tuple(sorted(tuple(map(int, term)) for term in a)),
            tuple(sorted(tuple(map(int, term)) for term in b)),
        )
    except (KeyError, TypeError, ValueError):
        return None


def _strict_milp_exact(row: dict[str, Any]) -> bool:
    details = row.get("milp_details")
    if not isinstance(details, dict) or not details:
        return bool(row.get("d_is_exact")) and row.get("stage") in {
            "exact", "milp_exact", "self_dual_d2", "symplectic_low_d"
        }
    total = int(details.get("total_logicals", 0) or 0)
    checked = int(details.get("num_logicals_checked", 0) or 0)
    optimal = int(details.get("logicals_optimal", 0) or 0)
    return bool(details.get("exact")) and total > 0 and checked == total == optimal


def _summary(values: list[float]) -> dict[str, float | None]:
    if not values:
        return {"mean": None, "median": None, "max": None}
    return {
        "mean": round(statistics.fmean(values), 6),
        "median": round(statistics.median(values), 6),
        "max": round(max(values), 6),
    }


def _load_reference(path: Path | None) -> list[dict[str, Any]]:
    if path is None or not path.is_file():
        return []
    data = json.loads(path.read_text())
    if isinstance(data, list):
        return data
    rows: list[dict[str, Any]] = []
    if isinstance(data, dict):
        for group, members in data.items():
            if isinstance(members, list):
                for member in members:
                    if isinstance(member, dict):
                        rows.append({"reference_group": group, **member})
    return rows


def _lean_metrics(lean_run_root: Path | None) -> dict[str, Any]:
    if lean_run_root is None or not lean_run_root.is_dir():
        return {"available": False}
    manifest = _read_json(lean_run_root / "manifest.json")
    objectives = _read_jsonl(lean_run_root / "objectives.jsonl")
    generated: dict[str, int] = {"css": 0, "exact": 0, "upper": 0}
    verified: dict[str, int] = {"css": 0, "exact": 0, "upper": 0}
    per_code: dict[str, dict[str, bool]] = {}
    for row in objectives:
        tier = str(row.get("qcode_tier", "unknown"))
        generated[tier] = generated.get(tier, 0) + 1
        source = lean_run_root / str(row.get("lean_file", ""))
        ok = source.with_suffix(".olean").is_file()
        if ok:
            verified[tier] = verified.get(tier, 0) + 1
        code_id = str(row.get("index") or row.get("source", {}).get("label") or source.stem)
        per_code.setdefault(code_id, {})[tier] = ok
    complete = sum(
        1 for tiers in per_code.values()
        if tiers.get("css") and (tiers.get("exact") or tiers.get("upper"))
    )
    total = sum(generated.values())
    passed = sum(verified.values())
    selected = int(manifest.get("selected_codes", len(per_code)) or 0)
    return {
        "available": True,
        "status": manifest.get("status", "unknown"),
        "selected_codes": selected,
        "objectives_generated": generated,
        "objectives_verified": verified,
        "objective_verification_rate": _ratio(passed, total),
        "exact_distance_lean_verification_rate": _ratio(verified.get("exact", 0), generated.get("exact", 0)),
        "upper_distance_lean_verification_rate": _ratio(verified.get("upper", 0), generated.get("upper", 0)),
        "complete_parameter_sets_verified": complete,
        "complete_parameter_lean_verification_rate": _ratio(complete, selected),
        "note": "A complete parameter set requires a verified CSS/rank objective and one verified exact-distance or distance-upper objective.",
    }


def compute_metrics(*, repo_dir: Path, run_id: str,
                    reference_catalog: Path | None = None,
                    lean_run_root: Path | None = None) -> dict[str, Any]:
    run_dir = repo_dir / "results" / "runs" / run_id
    rows = _read_jsonl(run_dir / "evaluations.jsonl")
    generations = _read_jsonl(run_dir / "generations.jsonl")
    run_meta = _read_json(run_dir / "run_meta.json")
    humanize_enabled = bool(run_meta.get("humanize"))
    humanize_state = _read_json(Path(run_meta.get("state_path", ""))) if humanize_enabled else {}
    archive_path = Path(run_meta.get("state_path", "")).parent / "elite-archive.json" if humanize_enabled else Path()
    humanize_archive = _read_json(archive_path) if humanize_enabled else {}
    valid = [row for row in rows if int(row.get("k", 0) or 0) > 0]
    distance_rows = [row for row in valid if int(row.get("d", 0) or 0) > 0]
    attempted = [
        row for row in distance_rows
        if row.get("milp_attempted") or isinstance(row.get("milp_details"), dict) and row.get("milp_details")
    ]
    exact = [row for row in attempted if _strict_milp_exact(row)]

    tightened = []
    exact_match = overestimated = underestimated = 0
    exact_factors: list[float] = []
    correction_factors: list[float] = []
    for row in attempted:
        bp = int(row.get("bp_osd_d", 0) or 0)
        final = int(row.get("d", 0) or 0)
        if bp > final > 0:
            tightened.append(row)
            correction_factors.append(bp / final)
    for row in exact:
        bp = int(row.get("bp_osd_d", 0) or 0)
        truth = int(row.get("d", 0) or 0)
        if bp == truth:
            exact_match += 1
        elif bp > truth:
            overestimated += 1
        elif 0 < bp < truth:
            underestimated += 1
        if bp > 0 and truth > 0:
            exact_factors.append(bp / truth)

    by_lattice: dict[tuple[int, int], int] = {}
    for row in valid:
        key = (int(row.get("ell", 0) or 0), int(row.get("m", 0) or 0))
        by_lattice[key] = max(by_lattice.get(key, 0), int(row.get("k", 0) or 0))

    reference = _load_reference(reference_catalog)
    reference_by_key = {_code_key(row): row for row in reference if _code_key(row) is not None}
    matched: list[tuple[dict[str, Any], dict[str, Any]]] = []
    for row in distance_rows:
        ref = reference_by_key.get(_code_key(row))
        if ref is not None:
            matched.append((row, ref))
    bp_agree = final_agree = ref_tightened = 0
    ref_factors: list[float] = []
    for row, ref in matched:
        ref_d = int(ref.get("ilp_d", 0) or 0)
        bp_d = int(row.get("bp_osd_d", row.get("d", 0)) or 0)
        final_d = int(row.get("d", 0) or 0)
        bp_agree += bp_d == ref_d and ref_d > 0
        final_agree += final_d == ref_d and ref_d > 0
        ref_tightened += bp_d > ref_d > 0
        if bp_d > 0 and ref_d > 0:
            ref_factors.append(bp_d / ref_d)

    if humanize_enabled:
        expected_lattices = int(run_meta.get("config", {}).get("max_rounds", 0) or 0)
        completed_lattices = int(run_meta.get("rounds_completed", 0) or 0)
        coverage_unit = "rlcr_rounds"
    else:
        expected_lattices = len(run_meta.get("config", {}).get("lattices", [])) or 18
        completed_lattices = len(generations)
        coverage_unit = "lattices"
    metrics = {
        "schema_version": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "run_id": run_id,
        "run_status": run_meta.get("status", "not-started" if not rows else "running"),
        "paper_protocol": {
            "bp_osd_semantics": "stochastic upper bound",
            "milp_exact_rule": "all 2k logical MILPs proven optimal (MIP gap = 0)",
            "paper_deep_milp_correction_baseline": {"corrected": 33, "audited": 149, "rate": round(33 / 149, 6)},
            "citation": "arxiv:2606.02418, Sections V-A/V-B and PBB deep-MILP audit",
        },
        "coverage": {
            "unit": coverage_unit,
            "expected_lattices": expected_lattices,
            "completed_lattices": completed_lattices,
            "lattice_completion_rate": _ratio(completed_lattices, expected_lattices),
            "evaluations_logged": len(rows),
            "valid_k_positive": len(valid),
            "distance_evaluated": len(distance_rows),
        },
        "humanize": {
            "enabled": humanize_enabled,
            "rounds_completed": int(run_meta.get("rounds_completed", 0) or 0),
            "unique_elite_cells": len(humanize_archive.get("cells", {})),
            "no_improvement_rounds": int(humanize_state.get("no_improvement_rounds", 0) or 0),
            "search_model": run_meta.get("config", {}).get("model"),
            "review_model": run_meta.get("config", {}).get("review_model"),
            "reasoning_effort": run_meta.get("config", {}).get("reasoning_effort"),
            "review_effort": run_meta.get("config", {}).get("review_effort"),
        },
        "search": {
            "valid_candidate_rate": _ratio(len(valid), len(rows)),
            "sigma_k_max_per_lattice": sum(by_lattice.values()),
            "max_k_by_lattice": {f"{ell},{m}": k for (ell, m), k in sorted(by_lattice.items())},
        },
        "milp_audit": {
            "attempted": len(attempted),
            "fully_certified_exact": len(exact),
            "exact_certification_rate": _ratio(len(exact), len(attempted)),
            "bp_osd_tightened": len(tightened),
            "tightening_rate": _ratio(len(tightened), len(attempted)),
            "tightening_factor": _summary(correction_factors),
        },
        "bp_osd_accuracy_on_exact_milp": {
            "ground_truth_codes": len(exact),
            "exact_matches": exact_match,
            "accuracy": _ratio(exact_match, len(exact)),
            "overestimates": overestimated,
            "overestimate_rate": _ratio(overestimated, len(exact)),
            "underestimates": underestimated,
            "reported_over_true_factor": _summary(exact_factors),
        },
        "reference_catalog_agreement": {
            "catalog_path": str(reference_catalog) if reference_catalog else None,
            "catalog_entries": len(reference),
            "matched_representations": len(matched),
            "bp_osd_agreements": bp_agree,
            "bp_osd_agreement_rate": _ratio(bp_agree, len(matched)),
            "final_bound_agreements": final_agree,
            "final_bound_agreement_rate": _ratio(final_agree, len(matched)),
            "bp_osd_tighter_than_catalog_count": ref_tightened,
            "bp_osd_over_catalog_factor": _summary(ref_factors),
            "warning": "Catalog ilp_d values can be certified exact or incumbent upper bounds; this is agreement, not an accuracy denominator.",
        },
        "lean": _lean_metrics(lean_run_root),
    }
    return metrics


def _markdown(metrics: dict[str, Any]) -> str:
    c = metrics["coverage"]
    m = metrics["milp_audit"]
    a = metrics["bp_osd_accuracy_on_exact_milp"]
    lean = metrics["lean"]
    pct = lambda value: "N/A" if value is None else f"{100 * value:.2f}%"
    return "\n".join([
        f"# QCode metrics: {metrics['run_id']}", "",
        f"- Run status: `{metrics['run_status']}`",
        f"- Coverage ({c.get('unit', 'lattices')}): {c['completed_lattices']}/{c['expected_lattices']} ({pct(c['lattice_completion_rate'])}), {c['evaluations_logged']} evaluations",
        f"- MILP audited: {m['attempted']}; fully exact: {m['fully_certified_exact']} ({pct(m['exact_certification_rate'])})",
        f"- BP-OSD tightened by MILP: {m['bp_osd_tightened']} ({pct(m['tightening_rate'])}); paper baseline: 33/149 (22.15%)",
        f"- BP-OSD accuracy on exact MILP ground truth: {a['exact_matches']}/{a['ground_truth_codes']} ({pct(a['accuracy'])})",
        f"- BP-OSD overestimates on exact ground truth: {a['overestimates']} ({pct(a['overestimate_rate'])})",
        f"- Lean objective verification: {pct(lean.get('objective_verification_rate'))}",
        f"- Complete [[n,k,d]]/[[n,k,<=d]] parameter sets Lean-verified: {lean.get('complete_parameter_sets_verified', 0)}/{lean.get('selected_codes', 0)} ({pct(lean.get('complete_parameter_lean_verification_rate'))})",
        "",
        "Accuracy uses only fully certified MILP distances as ground truth. Incumbent-only MILP and catalog upper bounds are reported separately as bound agreement.", "",
    ])


def write_metrics(*, repo_dir: Path, run_id: str,
                  reference_catalog: Path | None = None,
                  lean_run_root: Path | None = None) -> tuple[Path, Path]:
    metrics = compute_metrics(repo_dir=repo_dir, run_id=run_id,
                              reference_catalog=reference_catalog,
                              lean_run_root=lean_run_root)
    run_dir = repo_dir / "results" / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    json_path = run_dir / "metrics.json"
    md_path = run_dir / "metrics.md"
    json_path.write_text(json.dumps(metrics, ensure_ascii=False, indent=2) + "\n")
    md_path.write_text(_markdown(metrics))
    return json_path, md_path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-dir", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--reference-catalog", type=Path)
    parser.add_argument("--lean-run-root", type=Path)
    args = parser.parse_args()
    paths = write_metrics(repo_dir=args.repo_dir.resolve(), run_id=args.run_id,
                          reference_catalog=args.reference_catalog,
                          lean_run_root=args.lean_run_root)
    print("\n".join(map(str, paths)))


if __name__ == "__main__":
    main()
