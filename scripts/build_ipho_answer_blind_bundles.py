#!/usr/bin/env python3
"""Build sealed-controller and problem-only bundles for IPhO 2026.

The canonical input contains official grading material, so this utility is a
controller-side program and must not be copied into a solver workspace.  The
solver JSONL is constructed from an explicit allowlist.  In particular, the
canonical ``question`` field is intentionally ignored because its source
header names solution and marking-scheme files; a clean question is rebuilt
from ``shared_context`` and ``current_question`` instead.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Iterable


SCHEMA_VERSION = 1
PROTOCOL = "ipho-2026-answer-blind-v1"
DERIVE_POLICY = "derive_inline_from_problem_only_material"

# This ordered inventory is the controller commitment for the 28 formalization
# targets.  Both id and index are pinned even though they currently coincide.
EXPECTED_TARGETS: tuple[tuple[str, str, str], ...] = (
    ("ipho_2026_t1_a1", "ipho_2026_t1_a1", "T1"),
    ("ipho_2026_t1_b1", "ipho_2026_t1_b1", "T1"),
    ("ipho_2026_t1_b2", "ipho_2026_t1_b2", "T1"),
    ("ipho_2026_t1_c1", "ipho_2026_t1_c1", "T1"),
    ("ipho_2026_t1_c2", "ipho_2026_t1_c2", "T1"),
    ("ipho_2026_t2_a1", "ipho_2026_t2_a1", "T2"),
    ("ipho_2026_t2_b1", "ipho_2026_t2_b1", "T2"),
    ("ipho_2026_t2_b2", "ipho_2026_t2_b2", "T2"),
    ("ipho_2026_t2_b3", "ipho_2026_t2_b3", "T2"),
    ("ipho_2026_t2_c1", "ipho_2026_t2_c1", "T2"),
    ("ipho_2026_t2_c2", "ipho_2026_t2_c2", "T2"),
    ("ipho_2026_t2_c3", "ipho_2026_t2_c3", "T2"),
    ("ipho_2026_t2_c4", "ipho_2026_t2_c4", "T2"),
    ("ipho_2026_t3_a1", "ipho_2026_t3_a1", "T3"),
    ("ipho_2026_t3_a2", "ipho_2026_t3_a2", "T3"),
    ("ipho_2026_t3_a3", "ipho_2026_t3_a3", "T3"),
    ("ipho_2026_t3_b1", "ipho_2026_t3_b1", "T3"),
    ("ipho_2026_t3_b2", "ipho_2026_t3_b2", "T3"),
    ("ipho_2026_t3_c2", "ipho_2026_t3_c2", "T3"),
    ("ipho_2026_t3_c3", "ipho_2026_t3_c3", "T3"),
    ("ipho_2026_t3_c4", "ipho_2026_t3_c4", "T3"),
    ("ipho_2026_t3_c5", "ipho_2026_t3_c5", "T3"),
    ("ipho_2026_e1_a1", "ipho_2026_e1_a1", "E1"),
    ("ipho_2026_e1_a5", "ipho_2026_e1_a5", "E1"),
    ("ipho_2026_e1_b4", "ipho_2026_e1_b4", "E1"),
    ("ipho_2026_e1_b6", "ipho_2026_e1_b6", "E1"),
    ("ipho_2026_e1_c6", "ipho_2026_e1_c6", "E1"),
    ("ipho_2026_e1_c7", "ipho_2026_e1_c7", "E1"),
)

PAPER_ASSETS: dict[str, dict[str, str]] = {
    paper: {
        "problem_pdf": f"raw/{paper}_problem.pdf",
        "solution_pdf": f"raw/{paper}_solution.pdf",
    }
    for paper in ("T1", "T2", "T3", "E1")
}

GENERAL_INSTRUCTIONS_ASSET = "raw/theory_general_instructions.pdf"

# A future projection change fails closed if it introduces any controller-side
# semantic role below.  ``official_answer_seen`` is the sole exception and is
# accepted only with the literal value false.
FORBIDDEN_SOLVER_KEY_FRAGMENTS = (
    "answer",
    "solution",
    "marking",
    "rubric",
    "reasoning",
    "grader",
    "reusable_conclusion",
)


def _json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw_tmp = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    tmp = Path(raw_tmp)
    try:
        os.fchmod(fd, 0o600)
        with os.fdopen(fd, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp, path)
    finally:
        tmp.unlink(missing_ok=True)


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ValueError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
        if not isinstance(value, dict):
            raise ValueError(f"{path}:{line_no}: row must be a JSON object")
        rows.append(value)
    return rows


def _validate_inventory(rows: list[dict[str, Any]]) -> None:
    if len(rows) != len(EXPECTED_TARGETS):
        raise ValueError(
            f"expected exactly {len(EXPECTED_TARGETS)} ordered rows, found {len(rows)}"
        )
    for position, (row, expected) in enumerate(zip(rows, EXPECTED_TARGETS), 1):
        expected_id, expected_index, expected_paper = expected
        actual = (
            str(row.get("id") or "").strip(),
            str(row.get("index") or "").strip(),
            str(row.get("paper") or "").strip(),
        )
        if actual != expected:
            raise ValueError(
                "ordered inventory mismatch at row "
                f"{position}: expected {expected!r}, found {actual!r}"
            )
        expected_problem_id = f"ipho_2026_{expected_paper.lower()}"
        if str(row.get("problem_id") or "").strip() != expected_problem_id:
            raise ValueError(
                f"{expected_id}: expected problem_id {expected_problem_id!r}"
            )
        if row.get("formalization_ready") is not True:
            raise ValueError(f"{expected_id}: formalization_ready must be true")


def _asset_path(source_root: Path, relative: str) -> Path:
    candidate = Path(relative)
    if candidate.is_absolute() or ".." in candidate.parts:
        raise ValueError(f"asset path escapes source root: {relative}")
    root = source_root.resolve()
    resolved = (root / candidate).resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ValueError(f"asset path escapes source root: {relative}") from exc
    if not resolved.is_file():
        raise ValueError(f"missing source asset: {resolved}")
    return resolved


def _require_problem_text(row: dict[str, Any], key: str) -> str:
    value = row.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{row.get('id')}: missing non-empty {key}")
    return value.strip()


def _rebuilt_question(row: dict[str, Any]) -> str:
    shared_context = _require_problem_text(row, "shared_context")
    current_question = _require_problem_text(row, "current_question")
    part_id = str(row.get("part_id") or "").strip()
    heading = f"## Current subquestion {part_id}".rstrip()
    return (
        "## Physical scenario\n\n"
        f"{shared_context}\n\n"
        f"{heading}\n\n"
        f"{current_question}\n"
    )


def _sanitized_previous_parts(row: dict[str, Any]) -> list[dict[str, str]]:
    raw_parts = row.get("previous_parts") or []
    if not isinstance(raw_parts, list):
        raise ValueError(f"{row.get('id')}: previous_parts must be a list")
    sanitized: list[dict[str, str]] = []
    for position, raw in enumerate(raw_parts, 1):
        if not isinstance(raw, dict):
            raise ValueError(
                f"{row.get('id')}: previous_parts item {position} must be an object"
            )
        retained: dict[str, str] = {}
        for key in ("source_id", "part_id", "question"):
            value = raw.get(key)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(
                    f"{row.get('id')}: previous_parts item {position} "
                    f"is missing non-empty {key}"
                )
            retained[key] = value.strip()
        retained["dependency_policy"] = DERIVE_POLICY
        sanitized.append(retained)
    return sanitized


def _problem_assets(
    row: dict[str, Any], *, source_root: Path, paper: str
) -> tuple[list[str], list[dict[str, str]]]:
    expected_problem_rel = PAPER_ASSETS[paper]["problem_pdf"]
    declared_problem = str(row.get("source_pdf") or "").strip().replace("\\", "/")
    if PurePosixPath(declared_problem).name != Path(expected_problem_rel).name:
        raise ValueError(
            f"{row.get('id')}: source_pdf is not the {paper} problem PDF"
        )
    problem_pdf = _asset_path(source_root, expected_problem_rel)

    raw_images = row.get("images")
    if not isinstance(raw_images, list) or not raw_images:
        raise ValueError(f"{row.get('id')}: at least one question PNG is required")
    names: list[str] = []
    seen: set[str] = set()
    assets: list[dict[str, str]] = [
        {
            "kind": "problem_pdf",
            "path": expected_problem_rel,
            "sha256": _sha256_file(problem_pdf),
        }
    ]
    if paper != "E1":
        general_instructions = _asset_path(
            source_root, GENERAL_INSTRUCTIONS_ASSET
        )
        assets.append(
            {
                "kind": "problem_general_instructions",
                "path": GENERAL_INSTRUCTIONS_ASSET,
                "sha256": _sha256_file(general_instructions),
            }
        )
    for raw_name in raw_images:
        if not isinstance(raw_name, str) or not raw_name.strip():
            raise ValueError(f"{row.get('id')}: question PNG name must be non-empty")
        name = raw_name.strip().replace("\\", "/")
        path_value = PurePosixPath(name)
        if path_value.is_absolute() or len(path_value.parts) != 1 or ".." in path_value.parts:
            raise ValueError(f"{row.get('id')}: image path escapes image root: {name}")
        if not (name.startswith(f"{paper}_page-") and name.endswith(".png")):
            raise ValueError(
                f"{row.get('id')}: image is not a {paper} question-page PNG: {name}"
            )
        if name in seen:
            raise ValueError(f"{row.get('id')}: duplicate question PNG: {name}")
        seen.add(name)
        image_rel = f"image/{name}"
        image_path = _asset_path(source_root, image_rel)
        names.append(name)
        assets.append(
            {
                "kind": "problem_page",
                "path": image_rel,
                "sha256": _sha256_file(image_path),
            }
        )
    if str(row.get("image") or "").strip() != names[0]:
        raise ValueError(f"{row.get('id')}: image must equal the first images entry")
    return names, assets


def _blind_row(row: dict[str, Any], *, source_root: Path, paper: str) -> dict[str, Any]:
    images, assets = _problem_assets(row, source_root=source_root, paper=paper)
    shared_context = _require_problem_text(row, "shared_context")
    current_question = _require_problem_text(row, "current_question")
    return {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "phase": "solve",
        "id": str(row["id"]),
        "index": str(row["index"]),
        "source_index": str(row.get("source_index") or row.get("part_id") or ""),
        "problem_id": str(row.get("problem_id") or ""),
        "part_id": str(row.get("part_id") or ""),
        "question": _rebuilt_question(row),
        "current_question": current_question,
        "shared_context": shared_context,
        "category": str(row.get("category") or "IPhO 2026"),
        "dataset": "IPhO 2026 official English problem materials",
        "dataset_format": "native",
        "paper": paper,
        "kind": str(row.get("kind") or "theory"),
        "formalization_ready": bool(row.get("formalization_ready", True)),
        "image": images[0],
        "images": images,
        "previous_parts": _sanitized_previous_parts(row),
        "source_page": int(row.get("source_page") or 0),
        "printed_page": int(row.get("printed_page") or 0),
        "problem_assets": assets,
    }


def _assert_solver_safe(value: Any, *, path: str = "$") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            lowered = str(key).lower()
            if lowered == "official_answer_seen":
                if child is not False:
                    raise ValueError(
                        f"answer-blind integrity flag must be false at {path}.{key}"
                    )
                continue
            if any(fragment in lowered for fragment in FORBIDDEN_SOLVER_KEY_FRAGMENTS):
                raise ValueError(f"forbidden solver key at {path}.{key}")
            _assert_solver_safe(child, path=f"{path}.{key}")
    elif isinstance(value, list):
        for position, child in enumerate(value):
            _assert_solver_safe(child, path=f"{path}[{position}]")
    elif isinstance(value, str):
        normalized = value.lower().replace("\\", "/")
        looks_like_asset_reference = "/" in normalized or normalized.endswith(
            (".pdf", ".png", ".txt")
        )
        if looks_like_asset_reference and any(
            fragment in normalized
            for fragment in ("solution", "marking", "rubric", "grader", "answer_page")
        ):
            raise ValueError(f"forbidden controller asset reference at {path}")


def _grader_row(
    source: dict[str, Any],
    blind: dict[str, Any],
    *,
    source_root: Path,
    paper: str,
) -> dict[str, Any]:
    official_answer = source.get("answer")
    if not isinstance(official_answer, str) or not official_answer.strip():
        raise ValueError(f"{blind['id']}: missing official answer for controller grader")
    solution_rel = PAPER_ASSETS[paper]["solution_pdf"]
    declared_solution = str(source.get("solution_pdf") or "").strip().replace("\\", "/")
    if PurePosixPath(declared_solution).name != Path(solution_rel).name:
        raise ValueError(f"{blind['id']}: solution_pdf is not the {paper} solution PDF")
    solution_pdf = _asset_path(source_root, solution_rel)
    return {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "post_freeze_grade",
        "id": blind["id"],
        "index": blind["index"],
        "paper": paper,
        "blind_record_sha256": _sha256_bytes(_json_bytes(blind)),
        "official_answer": official_answer,
        "official_points": source.get("points"),
        "official_marking": source.get("marking"),
        "solution_pdf": solution_rel,
        "solution_pdf_sha256": _sha256_file(solution_pdf),
    }


def _manifest_path(jsonl_path: Path) -> Path:
    return jsonl_path.with_suffix(jsonl_path.suffix + ".manifest.json")


def build_bundles(
    *,
    input_jsonl: Path,
    blind_output: Path,
    grader_output: Path,
    source_root: Path,
) -> dict[str, Any]:
    if blind_output.resolve() == grader_output.resolve():
        raise ValueError("blind_output and grader_output must be separate paths")
    rows = _read_jsonl(input_jsonl)
    _validate_inventory(rows)

    blind_rows: list[dict[str, Any]] = []
    grader_rows: list[dict[str, Any]] = []
    targets: list[dict[str, str]] = []
    for source, (expected_id, expected_index, paper) in zip(rows, EXPECTED_TARGETS):
        blind = _blind_row(source, source_root=source_root, paper=paper)
        _assert_solver_safe(blind)
        blind_hash = _sha256_bytes(_json_bytes(blind))
        grader = _grader_row(
            source, blind, source_root=source_root, paper=paper
        )
        blind_rows.append(blind)
        grader_rows.append(grader)
        targets.append(
            {
                "id": expected_id,
                "index": expected_index,
                "paper": paper,
                "blind_record_sha256": blind_hash,
            }
        )

    blind_payload = b"".join(_json_bytes(row) for row in blind_rows)
    grader_payload = b"".join(_json_bytes(row) for row in grader_rows)
    blind_manifest = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "solve",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "row_count": len(blind_rows),
        "blind_output": blind_output.name,
        "blind_sha256": _sha256_bytes(blind_payload),
        "targets": targets,
    }
    _assert_solver_safe(blind_manifest)
    grader_manifest = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "post_freeze_grade",
        "row_count": len(grader_rows),
        "blind_output": blind_output.name,
        "blind_sha256": blind_manifest["blind_sha256"],
        "grader_output": grader_output.name,
        "grader_sha256": _sha256_bytes(grader_payload),
        "targets": targets,
        "solution_pdf_sha256": {
            paper: _sha256_file(
                _asset_path(source_root, PAPER_ASSETS[paper]["solution_pdf"])
            )
            for paper in PAPER_ASSETS
        },
    }

    # All validation and hashing finishes before any destination is replaced.
    _atomic_write(blind_output, blind_payload)
    _atomic_write(grader_output, grader_payload)
    _atomic_write(_manifest_path(blind_output), _json_bytes(blind_manifest))
    _atomic_write(_manifest_path(grader_output), _json_bytes(grader_manifest))
    return grader_manifest


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-jsonl", type=Path, required=True)
    parser.add_argument("--blind-output", type=Path, required=True)
    parser.add_argument("--grader-output", type=Path, required=True)
    parser.add_argument(
        "--source-root",
        type=Path,
        required=True,
        help="Directory containing the canonical raw/ and image/ assets.",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    manifest = build_bundles(
        input_jsonl=args.input_jsonl.resolve(),
        blind_output=args.blind_output.resolve(),
        grader_output=args.grader_output.resolve(),
        source_root=args.source_root.resolve(),
    )
    print(json.dumps(manifest, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
