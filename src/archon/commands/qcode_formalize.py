"""Bridge qcode-discovery results into Lean-checkable Archon artifacts.

The discovery stack is deliberately outside the trusted base: Python, BP-OSD,
and HiGHS select claims and produce witnesses. The generated Lean modules then
reconstruct and check those claims. Partial MILP runs are never promoted to an
exact-distance objective here.
"""
from __future__ import annotations
import concurrent.futures
import json
import os
import subprocess
from pathlib import Path
from typing import Any
from archon import log


def _code_key(row: dict[str, Any]) -> tuple[Any, ...]:
    def terms(name: str) -> tuple[tuple[int, int], ...]:
        return tuple(sorted(tuple(map(int, t)) for t in row.get(name, [])))
    return int(row["ell"]), int(row["m"]), terms("A_terms"), terms("B_terms")


def distance_is_exact(row: dict[str, Any]) -> bool:
    """Apply the paper's strict rule: every logical must be proven optimal."""
    if not row.get("d_is_exact"):
        return False
    details = row.get("milp_details")
    if not isinstance(details, dict) or not details:
        return row.get("stage") in {"exact", "self_dual_d2"} or (
            row.get("stage") == "symplectic_low_d" and int(row.get("d", 0)) == 2
        )
    total = int(details.get("total_logicals", 0) or 0)
    checked = int(details.get("num_logicals_checked", 0) or 0)
    optimal = int(details.get("logicals_optimal", 0) or 0)
    return bool(details.get("exact")) and total > 0 and checked == total and optimal == total


def load_evaluations(repo_dir: Path, run_id: str) -> list[dict[str, Any]]:
    path = repo_dir / "results" / "runs" / run_id / "evaluations.jsonl"
    if not path.is_file():
        raise FileNotFoundError(f"qcode run evaluations not found: {path}")
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def prepare_catalogs(rows: list[dict[str, Any]], limit: int) -> tuple[dict, dict]:
    """Select, deduplicate, normalize, and split exact versus upper claims."""
    valid = [row for row in rows
             if int(row.get("k", 0) or 0) > 0 and int(row.get("d", 0) or 0) > 0
             and row.get("A_terms") and row.get("B_terms")]
    audited = [row for row in valid if row.get("milp_attempted")]
    if audited:
        valid = audited
    novelty_checked = [
        row for row in valid
        if isinstance(row.get("structural_novelty"), dict)
        and row["structural_novelty"].get("checked") is True
    ]
    if novelty_checked:
        valid = [
            row for row in novelty_checked
            if row["structural_novelty"].get("novel") is True
        ]
    valid.sort(key=lambda row: float(row.get("score", 0) or 0), reverse=True)
    selected, seen = [], set()
    for row in valid:
        novelty = row.get("structural_novelty") or {}
        digest = novelty.get("canonical_digest")
        key = (
            "structural",
            int(row["n"]),
            int(row["k"]),
            digest,
        ) if digest else ("polynomial", *_code_key(row))
        if key in seen:
            continue
        seen.add(key); selected.append(row)
        if limit and len(selected) >= limit:
            break
    exact, upper = [], []
    for row in selected:
        n, k, d = int(row["n"]), int(row["k"]), int(row["d"])
        is_exact = distance_is_exact(row)
        normalized = {
            "label": f"[[{n},{k},{d}]]" if is_exact else f"[[{n},{k},<={d}]]",
            "ell": int(row["ell"]), "m": int(row["m"]),
            "A": row["A_terms"], "B": row["B_terms"], "k": k,
            "ilp_d": d, "d_is_exact": is_exact,
            "discovery_stage": row.get("stage"),
            "distance_source": row.get("distance_source", "bp_osd"),
            "score": row.get("score", 0),
            "structural_novelty": row.get("structural_novelty"),
        }
        (exact if is_exact else upper).append(normalized)
    return {"archon-qcode-exact": exact}, {"archon-qcode-upper": upper}


def _write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def _run(cmd: list[str], cwd: Path) -> None:
    log.step("$ " + " ".join(cmd))
    subprocess.run(cmd, cwd=cwd, check=True)


def _read_objectives(path: Path, tier: str) -> list[dict[str, Any]]:
    if not path.is_file():
        return []
    rows = []
    for line in path.read_text().splitlines():
        if line.strip():
            row = json.loads(line)
            row["lean_file"] = f"{tier}/{row['lean_file']}"
            row["qcode_tier"] = tier
            rows.append(row)
    return rows


def formalize_qcode_run(*, lean_project: Path, repo_dir: Path, bridge_dir: Path,
                         run_id: str, python: str, top: int,
                         witness_timeout: int, sat_timeout: int,
                         skip_missing: bool) -> Path:
    """Generate CSS, distance-upper, and exact-distance Lean modules."""
    release_manifest = repo_dir / "results" / "runs" / run_id / "challenge_manifest.json"
    _run([
        python,
        str(repo_dir / "scripts" / "check_release_manifest.py"),
        str(release_manifest),
        "--run-id", run_id,
    ], repo_dir)
    release = json.loads(release_manifest.read_text())
    rows = []
    for entry in release["certificates"]:
        certificate_path = release_manifest.parent / entry["file"]
        certificate = json.loads(certificate_path.read_text())
        if (
            certificate.get("passed") is not True
            or entry.get("verification", {}).get("passed") is not True
        ):
            raise RuntimeError(
                f"unverified challenge certificate cannot be formalized: {certificate_path}"
            )
        rows.append(certificate["claim"])
    if not rows:
        raise RuntimeError("verified challenge release contains no formalizable claims")
    exact_catalog, upper_catalog = prepare_catalogs(rows, top)
    all_catalog = {"archon-qcode": exact_catalog["archon-qcode-exact"]
                   + upper_catalog["archon-qcode-upper"]}
    run_root = lean_project / ".archon" / "qcode-runs" / run_id
    run_root.mkdir(parents=True, exist_ok=True)
    _write_json(run_root / "catalog.json", all_catalog)
    _write_json(run_root / "exact-catalog.json", exact_catalog)
    _write_json(run_root / "upper-catalog.json", upper_catalog)
    css_out = run_root / "css"
    _run([python, str(bridge_dir / "bridge_css.py"), "--catalog",
          str(run_root / "catalog.json"), "--out", str(css_out)], bridge_dir)
    exact_count = len(exact_catalog["archon-qcode-exact"])
    if exact_count:
        cmd = [python, str(bridge_dir / "bridge_exact.py"), "--catalog",
               str(run_root / "exact-catalog.json"), "--out", str(run_root / "exact"),
               "--search-timeout", str(witness_timeout), "--sat-timeout", str(sat_timeout)]
        if skip_missing: cmd.append("--skip-missing")
        _run(cmd, bridge_dir)
    upper_count = len(upper_catalog["archon-qcode-upper"])
    if upper_count:
        cmd = [python, str(bridge_dir / "bridge_distance.py"), "--catalog",
               str(run_root / "upper-catalog.json"), "--out", str(run_root / "upper"),
               "--target-field", "ilp_d", "--timeout", str(witness_timeout)]
        if skip_missing: cmd.append("--skip-missing")
        _run(cmd, bridge_dir)
    objectives = _read_objectives(css_out / "objectives.jsonl", "css")
    objectives += _read_objectives(run_root / "exact" / "objectives.jsonl", "exact")
    objectives += _read_objectives(run_root / "upper" / "objectives.jsonl", "upper")
    with (run_root / "objectives.jsonl").open("w") as stream:
        for row in objectives: stream.write(json.dumps(row, ensure_ascii=False) + "\n")
    manifest = {"run_id": run_id, "source_evaluations": len(rows),
                "selected_codes": len(all_catalog["archon-qcode"]),
                "exact_claims": exact_count, "upper_bound_claims": upper_count,
                "lean_objectives": len(objectives), "status": "formalized"}
    _write_json(run_root / "manifest.json", manifest)
    log.success(f"Formalized {manifest['selected_codes']} qcodes: "
                f"{exact_count} exact, {upper_count} upper-bound")
    return run_root


def _compile_one(lean_project: Path, tier_root: Path, source: Path,
                 log_path: Path) -> tuple[Path, bool]:
    env = os.environ.copy()
    env["LEAN_PATH"] = str(tier_root) + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    with log_path.open("w") as stream:
        proc = subprocess.run(["lake", "env", "lean", "-o", str(source.with_suffix('.olean')),
                               str(source)], cwd=lean_project, env=env,
                              stdout=stream, stderr=subprocess.STDOUT)
    return source, proc.returncode == 0


def verify_qcode_run(lean_project: Path, run_root: Path, jobs: int) -> dict[str, int]:
    """Compile every generated theorem; this is the Lean proof-checking gate."""
    if not 1 <= jobs <= 4:
        raise ValueError("Lean jobs must be between 1 and 4")
    log_dir = run_root / "lean-logs"; log_dir.mkdir(exist_ok=True)
    for tier, lib in (("exact", "QExact"), ("upper", "QDistance")):
        basic = run_root / tier / lib / "Basic.lean"
        if basic.is_file():
            _, ok = _compile_one(lean_project, run_root / tier, basic,
                                 log_dir / f"{tier}-Basic.log")
            if not ok: raise RuntimeError(f"Lean failed on {basic}; see {log_dir}")
    objectives = [json.loads(line) for line in (run_root / "objectives.jsonl").read_text().splitlines()
                  if line.strip()]
    tasks = []
    for row in objectives:
        source = run_root / row["lean_file"]
        tier = row["qcode_tier"]
        tasks.append((run_root / tier, source, log_dir / f"{tier}-{source.stem}.log"))
    passed = failed = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = [pool.submit(_compile_one, lean_project, tier_root, source, path)
                   for tier_root, source, path in tasks]
        for future in concurrent.futures.as_completed(futures):
            source, ok = future.result()
            if ok:
                passed += 1; log.info(f"Lean verified: {source.name}")
            else:
                failed += 1; log.warn(f"Lean failed: {source}")
    manifest_path = run_root / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest.update({"lean_verified": passed, "lean_failed": failed,
                     "status": "verified" if failed == 0 else "lean-failed"})
    _write_json(manifest_path, manifest)
    if failed: raise RuntimeError(f"{failed} qcode Lean objectives failed; see {log_dir}")
    log.success(f"Lean verified all {passed} generated qcode objectives")
    return {"passed": passed, "failed": failed}
