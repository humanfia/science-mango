#!/usr/bin/env python3
"""Merge exact DistQLDPC and anchored SAT evidence into a Stage 3 claim.

This command never invokes a solver.  It rebuilds the candidate and all CSS
context from the supplied candidate input, freshly verifies both terminal
checkpoints, and only then delegates composition to the production Stage 3
artifact and Stage 3-to-Stage 4 claim adapters.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import sys
import time
from collections.abc import Mapping
from pathlib import Path
from typing import Any

import numpy as np


PROJECT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT))

from evaluation.bb_sector_isometry import (  # noqa: E402
    verify_bb_xz_sector_isometry,
)
from evaluation.css_logical_detector import (  # noqa: E402
    verify_css_logical_detectors,
)
from evaluation.distance_distqldpc import (  # noqa: E402
    DISTQLDPC_CARDINALITY_MODES,
    verify_distqldpc_exact_evidence,
    verify_distqldpc_lower_evidence,
)
from evaluation.distance_milp import get_code_matrices  # noqa: E402
from evaluation.distance_sat import (  # noqa: E402
    SAT_NATIVE_THREAD_ENV,
    _instance_binding as sat_instance_binding,
    verify_css_threshold_sat_witness,
)
from evaluation.geometry import candidate_geometry  # noqa: E402
from evaluation.proof_runtime import (  # noqa: E402
    proof_runtime_fingerprint,
    validate_proof_runtime_fingerprint,
)
from evaluation.sector_certificate import (  # noqa: E402
    REQUEST_FIELD as SECTOR_REQUEST_FIELD,
    claim_from_sector_sat_artifact,
)
from evaluation.structural_dedup import (  # noqa: E402
    canonical_digest as code_canonical_digest,
)
from evaluation.target_policy import (  # noqa: E402
    TARGET_MODE_SCALAR_13_INCLUSIVE,
)
from scripts.audit_direction_pool import candidate_from_stage2  # noqa: E402
from scripts.screen_frontier_candidate import (  # noqa: E402
    build_candidate_code,
    validate_candidate_parameters,
)
from scripts.screen_frontier_sat import (  # noqa: E402
    SAT_COVERAGE_MODES,
    SAT_STAGE3_GATE,
    _admissibility_checkpoint_fields,
    _artifact,
    _proof_plan,
    build_anchor_cover_cubes,
    distqldpc_stage3_checkpoint_identity,
)
from scripts.screen_frontier_xor import (  # noqa: E402
    verify_bb_translation_symmetry,
)


SCHEMA_VERSION = 1
MANIFEST_GATE = "qcode-distqldpc-stage3-merge-v1"
SEAL_GATE = "qcode-distqldpc-stage3-merge-seal-v1"
TERMINAL_SEAL_GATE = "qcode-distqldpc-stage3-merged-terminal-v1"


def _canonical_sha256(value: Any, *, omit: str | None = None) -> str:
    payload = dict(value) if isinstance(value, Mapping) else value
    if omit is not None and isinstance(payload, dict):
        payload.pop(omit, None)
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _json_bytes(value: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(
            dict(value),
            indent=2,
            sort_keys=True,
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode()


def _bytes_sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _strict_json(text: str, *, source: Path) -> Any:
    def object_without_duplicates(
        pairs: list[tuple[str, Any]],
    ) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key {key!r} in {source}")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number {value!r} in {source}")

    return json.loads(
        text,
        object_pairs_hook=object_without_duplicates,
        parse_constant=reject_constant,
    )


def _resolve_input(path: Path, *, label: str) -> Path:
    try:
        resolved = path.expanduser().resolve(strict=True)
    except OSError as exc:
        raise ValueError(f"{label} is unavailable: {path}: {exc}") from exc
    if not resolved.is_file():
        raise ValueError(f"{label} is not a regular file: {resolved}")
    return resolved


def _load_json_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = _strict_json(path.read_text(encoding="utf-8"), source=path)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError(f"invalid {label}: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be one JSON object")
    return value


def _load_candidate_rows(path: Path) -> list[dict[str, Any]]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise ValueError(f"candidate input is unreadable: {exc}") from exc
    try:
        value = _strict_json(text, source=path)
    except json.JSONDecodeError:
        rows: list[dict[str, Any]] = []
        for line_number, line in enumerate(text.splitlines(), start=1):
            if not line.strip():
                continue
            try:
                row = _strict_json(line, source=path)
            except (json.JSONDecodeError, ValueError) as exc:
                raise ValueError(
                    f"candidate JSONL {path}:{line_number} is invalid: {exc}",
                ) from exc
            if not isinstance(row, dict):
                raise ValueError(
                    f"candidate JSONL {path}:{line_number} is not an object",
                )
            rows.append(row)
        return rows
    except ValueError as exc:
        raise ValueError(f"candidate input is invalid: {exc}") from exc
    if isinstance(value, dict):
        return [value]
    if isinstance(value, list) and all(isinstance(row, dict) for row in value):
        return [dict(row) for row in value]
    raise ValueError("candidate input must be a JSON object, list, or JSONL")


def _candidate_from_input(
    path: Path,
    *,
    index: int,
    stage2_ranked: bool,
    target_mode: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    rows = _load_candidate_rows(path)
    if not 0 <= index < len(rows):
        raise ValueError(
            f"candidate index {index} is unavailable in {len(rows)} rows",
        )
    row = rows[index]
    if stage2_ranked or isinstance(row.get("campaign_audit"), Mapping):
        candidate = candidate_from_stage2(row, target_mode=target_mode)
        input_kind = "stage2-ranked"
    elif (
        row.get("gate") == SAT_STAGE3_GATE
        and isinstance(row.get("candidate"), Mapping)
    ):
        candidate = dict(row["candidate"])
        input_kind = "stage3-candidate"
    else:
        candidate = dict(row)
        input_kind = "candidate"
    return candidate, {
        "kind": input_kind,
        "path": str(path),
        "file_sha256": _file_sha256(path),
        "row_index": index,
        "row_sha256": _canonical_sha256(row),
        "rows": len(rows),
    }


def _matrix_record(matrix: np.ndarray) -> dict[str, Any]:
    binary = np.asarray(matrix, dtype=np.uint8) & 1
    packed = np.packbits(binary, axis=None, bitorder="little").tobytes()
    return {
        "shape": list(binary.shape),
        "packed_sha256": hashlib.sha256(packed).hexdigest(),
    }


def _fresh_context(
    candidate: dict[str, Any],
    *,
    expected_digest: str | None,
    coverage_mode: str,
) -> dict[str, Any]:
    if candidate.get("C_terms") or candidate.get("D_terms"):
        raise ValueError("DistQLDPC Stage 3 merge accepts CSS candidates only")
    if isinstance(candidate.get("construction"), Mapping):
        raise ValueError(
            "single-sector anchored merge currently requires a CSS BB candidate",
        )
    if candidate.get("target_mode") != TARGET_MODE_SCALAR_13_INCLUSIVE:
        raise ValueError(
            "candidate target_mode must be scalar-fom-13-inclusive-v1",
        )
    code = build_candidate_code(copy.deepcopy(candidate))
    geometry = validate_candidate_parameters(candidate, code)
    rebuilt_digest = code_canonical_digest(code)
    declared_digest = candidate.get("canonical_digest")
    if not isinstance(declared_digest, str) or rebuilt_digest != declared_digest:
        raise ValueError("fresh canonical digest differs from the candidate")
    if expected_digest is not None and rebuilt_digest != expected_digest:
        raise ValueError("fresh canonical digest differs from the explicit expectation")

    matrices = tuple(
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    hx, hz, lx, lz = matrices
    detector = verify_css_logical_detectors(hx, hz, lx, lz)
    if detector.get("verified") is not True:
        raise ValueError("fresh CSS logical detector replay failed")
    symmetry = verify_bb_translation_symmetry(copy.deepcopy(candidate))
    if symmetry.get("verified") is not True:
        raise ValueError("fresh BB translation-symmetry replay failed")
    raw_anchors = symmetry.get("orbit_representatives")
    if not isinstance(raw_anchors, list) or not raw_anchors:
        raise ValueError("fresh translation symmetry has no orbit representatives")
    anchors = tuple(int(index) for index in raw_anchors)
    if len(set(anchors)) != len(anchors):
        raise ValueError("fresh translation orbit representatives are duplicated")
    isometry = verify_bb_xz_sector_isometry(
        hx,
        hz,
        ell=int(candidate["ell"]),
        m=int(candidate["m"]),
        geometry=candidate_geometry(candidate),
    )
    if not (
        isometry.get("verified") is True
        and isometry.get("canonical_sector") == "X"
        and isometry.get("covered_sectors") == ["X", "Z"]
    ):
        raise ValueError(
            "single upper-X checkpoint requires a fresh complete X/Z isometry",
        )
    cubes = build_anchor_cover_cubes(anchors)
    plan = _proof_plan(
        coverage_mode,
        int(geometry["k"]),
        ("X",),
        cubes,
        "distqldpc",
    )
    return {
        "candidate": candidate,
        "geometry": geometry,
        "matrices": matrices,
        "detector": detector,
        "symmetry": symmetry,
        "isometry": isometry,
        "anchors": anchors,
        "anchor_cover_cubes": cubes,
        "plan": plan,
        "matrix_binding": {
            name: _matrix_record(matrix)
            for name, matrix in zip(("Hx", "Hz", "Lx", "Lz"), matrices)
        },
    }


def _expected_upper_identity(context: Mapping[str, Any]) -> dict[str, Any]:
    candidate = context["candidate"]
    target = candidate.get("target")
    return {
        "stage3_gate": SAT_STAGE3_GATE,
        "candidate_digest": candidate["canonical_digest"],
        "target_mode": candidate.get("target_mode"),
        "target_binding_sha256": (
            target.get("binding_sha256")
            if isinstance(target, Mapping)
            else None
        ),
        **_admissibility_checkpoint_fields(candidate),
        "phase": "upper",
        "coverage_mode": context["coverage_mode"],
        "logical_detector_sha256": context["detector"]["report_sha256"],
        "translation_symmetry": context["symmetry"],
        "construction_symmetry_sha256": None,
        "xz_sector_isometry_sha256": context["isometry"]["report_sha256"],
    }


def _verify_upper(
    evidence: dict[str, Any],
    context: Mapping[str, Any],
) -> None:
    _hx, hz, _lx, lz = context["matrices"]
    required = int(context["candidate"]["required_distance"])
    anchors = tuple(context["anchors"])
    if (
        evidence.get("outcome") != "sat"
        or evidence.get("decision_complete") is not True
        or evidence.get("retryable") is not False
        or evidence.get("sector") != "X"
        or evidence.get("partition_index") is not None
        or evidence.get("anchor_indices") != list(anchors)
        or evidence.get("max_weight") != required
        or evidence.get("objective") != required
    ):
        raise ValueError("anchored upper checkpoint is not a terminal weight-R X witness")
    failures = verify_css_threshold_sat_witness(evidence, hz, lz)
    if failures:
        raise ValueError("anchored upper witness replay failed: " + "; ".join(failures))
    instance = evidence.get("instance")
    backend = evidence.get("backend")
    if not isinstance(instance, Mapping) or not isinstance(backend, Mapping):
        raise ValueError("anchored upper checkpoint lacks an instance/backend binding")
    expected_identity = _expected_upper_identity(context)
    if instance.get("checkpoint_identity") != expected_identity:
        raise ValueError("anchored upper checkpoint identity does not replay")
    native_environment = instance.get("native_thread_environment")
    if not (
        isinstance(native_environment, Mapping)
        and set(native_environment) == set(SAT_NATIVE_THREAD_ENV)
        and all(native_environment.get(name) == "1" for name in SAT_NATIVE_THREAD_ENV)
    ):
        raise ValueError("anchored upper checkpoint lacks the full thread=1 binding")
    execution = instance.get("solver_execution")
    incremental_budget = (
        execution.get("incremental_conflict_budget")
        if isinstance(execution, Mapping)
        else None
    )
    fresh_instance = sat_instance_binding(
        hz,
        lz,
        max_weight=required,
        sector="X",
        encoding=str(evidence.get("cardinality_encoding")),
        solver_name=str(backend.get("solver")),
        incremental_conflict_budget=incremental_budget,
        checkpoint_identity=expected_identity,
        partition_index=None,
        anchor_indices=anchors,
    )
    fresh_instance["native_thread_environment"] = dict(native_environment)
    fresh_instance["binding_sha256"] = _canonical_sha256(
        fresh_instance,
        omit="binding_sha256",
    )
    if dict(instance) != fresh_instance:
        raise ValueError("anchored upper SAT instance binding does not replay")


def _verify_distqldpc(
    evidence: dict[str, Any],
    context: Mapping[str, Any],
    *,
    cardinality_mode: str,
) -> dict[str, Any]:
    hx, hz, lx, lz = context["matrices"]
    candidate = context["candidate"]
    identity = distqldpc_stage3_checkpoint_identity(
        candidate,
        cardinality_mode=cardinality_mode,
        coverage_mode=context["coverage_mode"],
        logical_detector=context["detector"],
        translation_symmetry=context["symmetry"],
        construction_symmetry=None,
        xz_sector_isometry=context["isometry"],
    )
    exact_failures = verify_distqldpc_exact_evidence(
        evidence,
        hx,
        hz,
        lx,
        lz,
        max_weight=int(candidate["required_distance"]) - 1,
        cardinality_mode=cardinality_mode,
        expected_checkpoint_identity=identity,
    )
    lower_failures = verify_distqldpc_lower_evidence(
        evidence,
        hx,
        hz,
        lx,
        lz,
        max_weight=int(candidate["required_distance"]) - 1,
        cardinality_mode=cardinality_mode,
        expected_checkpoint_identity=identity,
    )
    if exact_failures or lower_failures:
        failures = [
            *(f"exact: {item}" for item in exact_failures),
            *(f"lower: {item}" for item in lower_failures),
        ]
        raise ValueError("DistQLDPC checkpoint replay failed: " + "; ".join(failures))
    distance = evidence.get("exact_distance")
    if distance != int(candidate["required_distance"]):
        raise ValueError(
            "DistQLDPC exact distance does not equal the required/upper distance",
        )
    return identity


def _loaded_project_source_hashes() -> dict[str, str]:
    paths: set[Path] = {Path(__file__).resolve()}
    for module in tuple(sys.modules.values()):
        raw = getattr(module, "__file__", None)
        if not isinstance(raw, str):
            continue
        try:
            path = Path(raw).resolve(strict=True)
            path.relative_to(PROJECT)
        except (OSError, ValueError):
            continue
        if path.suffix == ".py" and path.is_file():
            paths.add(path)
    return {
        str(path.relative_to(PROJECT)): _file_sha256(path)
        for path in sorted(paths)
    }


def _write_new_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = _json_bytes(value)
    with path.open("xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--candidate", type=Path)
    source.add_argument("--stage2-ranked", type=Path)
    parser.add_argument("--candidate-index", type=int, default=0)
    parser.add_argument("--expected-canonical-digest")
    parser.add_argument("--mto-checkpoint", type=Path, required=True)
    parser.add_argument("--anchored-upper-checkpoint", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument(
        "--cardinality-mode",
        choices=tuple(DISTQLDPC_CARDINALITY_MODES),
        required=True,
    )
    parser.add_argument(
        "--coverage-mode",
        choices=tuple(sorted(SAT_COVERAGE_MODES)),
        required=True,
    )
    parser.add_argument(
        "--target-mode",
        choices=(TARGET_MODE_SCALAR_13_INCLUSIVE,),
        default=TARGET_MODE_SCALAR_13_INCLUSIVE,
    )
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="freshly replay and compose in memory without writing output",
    )
    return parser


def _run(args: argparse.Namespace) -> dict[str, Any]:
    candidate_argument = args.stage2_ranked or args.candidate
    assert candidate_argument is not None
    candidate_path = _resolve_input(candidate_argument, label="candidate input")
    mto_path = _resolve_input(args.mto_checkpoint, label="MTO checkpoint")
    upper_path = _resolve_input(
        args.anchored_upper_checkpoint,
        label="anchored upper checkpoint",
    )
    output_root = args.output_root.expanduser().resolve(strict=False)
    if not args.check_only and output_root.exists():
        raise ValueError(f"output root already exists: {output_root}")

    candidate, candidate_input = _candidate_from_input(
        candidate_path,
        index=args.candidate_index,
        stage2_ranked=args.stage2_ranked is not None,
        target_mode=args.target_mode,
    )
    context = _fresh_context(
        candidate,
        expected_digest=args.expected_canonical_digest,
        coverage_mode=args.coverage_mode,
    )
    context["coverage_mode"] = args.coverage_mode
    mto = _load_json_object(mto_path, label="MTO checkpoint")
    upper = _load_json_object(upper_path, label="anchored upper checkpoint")
    mto_identity = _verify_distqldpc(
        mto,
        context,
        cardinality_mode=args.cardinality_mode,
    )
    _verify_upper(upper, context)

    digest = str(candidate["canonical_digest"])
    lower_unit_id = f"lower-distqldpc-{args.cardinality_mode}-XZ-global"
    units = {
        lower_unit_id: {
            "unit_id": lower_unit_id,
            "phase": f"lower-distqldpc-{args.cardinality_mode}",
            "sector": "XZ",
            "partition_index": None,
            "anchor_cube": None,
            "solver_evidence": mto,
            "attempts": [],
        },
        "upper-X-global": {
            "unit_id": "upper-X-global",
            "phase": "upper",
            "sector": "X",
            "partition_index": None,
            "anchor_cube": None,
            "solver_evidence": upper,
            "attempts": [],
        },
    }
    started = time.monotonic()
    hx, hz, lx, lz = context["matrices"]
    artifact = _artifact(
        candidate,
        mode=args.coverage_mode,
        translation_symmetry=context["symmetry"],
        construction_symmetry=None,
        logical_detector=context["detector"],
        units=units,
        expected_units=len(context["plan"]),
        started=started,
        xz_sector_isometry=context["isometry"],
        proof_sectors=("X",),
        anchor_cover_cubes=context["anchor_cover_cubes"],
        lower_backend="distqldpc",
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
    )
    if not (
        artifact.get("status") == "EXACT_PROVEN"
        and artifact.get("lower_bound_backend") == "distqldpc"
        and artifact.get("distqldpc_exact_distances")
        == [int(candidate["required_distance"])]
    ):
        raise ValueError("production Stage 3 composition did not prove exact distance")
    claim = claim_from_sector_sat_artifact(artifact)
    request = claim.get(SECTOR_REQUEST_FIELD)
    if not (
        isinstance(request, Mapping)
        and request.get("stage3_status") == "EXACT_PROVEN"
        and request.get("lower_bound_backend") == "distqldpc"
        and request.get("stage3_artifact_sha256")
        == _canonical_sha256(artifact)
    ):
        raise ValueError("production Stage 3-to-Stage 4 claim binding failed")

    proof_runtime = validate_proof_runtime_fingerprint(
        proof_runtime_fingerprint(),
    )
    source_files = _loaded_project_source_hashes()
    stage3_path = output_root / "stage3-exact-proven.json"
    claim_path = output_root / "publication-claim-preflight.json"
    terminal_path = output_root / "merged-terminal.schema-seal.json"
    manifest_path = output_root / "input/merge-handoff.json"
    schema_seal_path = output_root / "input/merge-handoff.schema-seal.json"
    stage3_bytes = _json_bytes(artifact)
    claim_bytes = _json_bytes(claim)
    manifest: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "gate": MANIFEST_GATE,
        "status": "COMPLETE",
        "solver_invoked": False,
        "canonical_digest": digest,
        "resolved_arguments": {
            "candidate_input": str(candidate_path),
            "candidate_index": args.candidate_index,
            "mto_checkpoint": str(mto_path),
            "anchored_upper_checkpoint": str(upper_path),
            "output_root": str(output_root),
            "cardinality_mode": args.cardinality_mode,
            "coverage_mode": args.coverage_mode,
            "target_mode": args.target_mode,
        },
        "candidate_input": candidate_input,
        "mto": {
            "path": str(mto_path),
            "file_sha256": _file_sha256(mto_path),
            "evidence_sha256": mto["evidence_sha256"],
            "checkpoint_identity": mto_identity,
            "checkpoint_identity_sha256": _canonical_sha256(mto_identity),
            "exact_distance": mto["exact_distance"],
            "fresh_exact_failures": [],
            "fresh_lower_failures": [],
        },
        "anchored_upper": {
            "path": str(upper_path),
            "file_sha256": _file_sha256(upper_path),
            "evidence_sha256": upper["evidence_sha256"],
            "operator_sha256": upper["operator"]["sha256"],
            "objective": upper["objective"],
            "anchor_indices": list(context["anchors"]),
            "fresh_failures": [],
        },
        "fresh_context": {
            "n": int(context["geometry"]["n"]),
            "k": int(context["geometry"]["k"]),
            "required_distance": int(candidate["required_distance"]),
            "matrix_binding": context["matrix_binding"],
            "logical_detector_sha256": context["detector"]["report_sha256"],
            "translation_symmetry_sha256": _canonical_sha256(context["symmetry"]),
            "xz_sector_isometry_sha256": context["isometry"]["report_sha256"],
            "anchor_cube_sha256": [
                cube["cube_sha256"] for cube in context["anchor_cover_cubes"]
            ],
            "proof_sectors": ["X"],
            "expected_units": len(context["plan"]),
        },
        "production_composition": {
            "artifact_helper": "scripts.screen_frontier_sat._artifact",
            "claim_helper": (
                "evaluation.sector_certificate.claim_from_sector_sat_artifact"
            ),
            "stage3_status": artifact["status"],
            "stage3_artifact_sha256": artifact["artifact_sha256"],
            "claim_stage3_binding_sha256": request["stage3_artifact_sha256"],
        },
        "outputs": {
            "stage3": {
                "path": str(stage3_path),
                "file_sha256": _bytes_sha256(stage3_bytes),
                "artifact_sha256": artifact["artifact_sha256"],
            },
            "claim": {
                "path": str(claim_path),
                "file_sha256": _bytes_sha256(claim_bytes),
            },
            "terminal_seal": str(terminal_path),
        },
        "source_provenance": {
            "entrypoint": str(Path(__file__).resolve()),
            "argv": list(sys.argv),
            "source_files": source_files,
            "proof_runtime": proof_runtime,
        },
    }
    manifest["manifest_sha256"] = _canonical_sha256(manifest)
    manifest_bytes = _json_bytes(manifest)
    schema_seal: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "gate": SEAL_GATE,
        "status": "COMPLETE",
        "solver_invoked": False,
        "canonical_digest": digest,
        "manifest_path": str(manifest_path),
        "manifest_file_sha256": _bytes_sha256(manifest_bytes),
        "manifest_sha256": manifest["manifest_sha256"],
        "stage3_file_sha256": _bytes_sha256(stage3_bytes),
        "claim_file_sha256": _bytes_sha256(claim_bytes),
    }
    schema_seal["seal_sha256"] = _canonical_sha256(schema_seal)
    terminal: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "gate": TERMINAL_SEAL_GATE,
        "status": "COMPLETE",
        "solver_invoked": False,
        "canonical_digest": digest,
        "stage3_status": artifact["status"],
        "stage3_path": str(stage3_path),
        "stage3_file_sha256": _bytes_sha256(stage3_bytes),
        "stage3_artifact_sha256": artifact["artifact_sha256"],
        "claim_path": str(claim_path),
        "claim_file_sha256": _bytes_sha256(claim_bytes),
        "manifest_file_sha256": _bytes_sha256(manifest_bytes),
        "manifest_sha256": manifest["manifest_sha256"],
        "source_entrypoint_sha256": source_files[
            str(Path(__file__).resolve().relative_to(PROJECT))
        ],
    }
    terminal["seal_sha256"] = _canonical_sha256(terminal)

    if _loaded_project_source_hashes() != source_files:
        raise ValueError("loaded project source files changed during merge")
    summary = {
        "status": "CHECKED" if args.check_only else "COMPLETE",
        "solver_invoked": False,
        "output_root": str(output_root),
        "canonical_digest": digest,
        "distance": int(candidate["required_distance"]),
        "stage3_file_sha256": _bytes_sha256(stage3_bytes),
        "stage3_artifact_sha256": artifact["artifact_sha256"],
        "claim_file_sha256": _bytes_sha256(claim_bytes),
        "manifest_file_sha256": _bytes_sha256(manifest_bytes),
        "manifest_sha256": manifest["manifest_sha256"],
        "terminal_seal_sha256": terminal["seal_sha256"],
    }
    if args.check_only:
        return summary

    output_root.mkdir(parents=True, exist_ok=False)
    _write_new_json(stage3_path, artifact)
    _write_new_json(claim_path, claim)
    _write_new_json(manifest_path, manifest)
    _write_new_json(schema_seal_path, schema_seal)
    _write_new_json(terminal_path, terminal)
    if not (
        _file_sha256(stage3_path) == summary["stage3_file_sha256"]
        and _file_sha256(claim_path) == summary["claim_file_sha256"]
        and _file_sha256(manifest_path) == summary["manifest_file_sha256"]
    ):
        raise ValueError("written merge output differs from its sealed bytes")
    return summary


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    try:
        result = _run(args)
    except (
        KeyError,
        OSError,
        RuntimeError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
    ) as exc:
        print(f"DISTQLDPC STAGE3 MERGE FAILED: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
