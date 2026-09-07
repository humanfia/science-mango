#!/usr/bin/env python3
"""Build a minimal IPhO 2026 problem-only solver seed.

This is a controller-side utility.  It verifies the sealed controller's blind
JSONL and blind manifest, then copies only a fixed Lean 4.31 skeleton and the
problem assets committed to by those rows.  The input asset directory may also
contain solutions and marking schemes; they are never traversed or copied.

The output is not a Git repository.  Its manifest requires the consumer to use
a fresh, history-free, remote-free ``git init``.  Runtime code, credentials,
old Lean targets, reports, references, and controller grading data are outside
the seed by construction.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import stat
import tempfile
import tomllib
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, NamedTuple, Sequence
from urllib.parse import urlsplit

SCHEMA_VERSION = 1
PROTOCOL = "icho-problem-only-solver-seed-v1"
BLIND_PROTOCOL = "ipho-2026-answer-blind-v1"
MANIFEST_NAME = "isolation_manifest.json"
BUNDLE_DESTINATION = "ipho_2026_source/questions_only.jsonl"
ASSET_DESTINATION_ROOT = "ipho_2026_source"
LEAN_VERSION = "leanprover/lean4:v4.31.0"
MATHLIB_REV = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
PHYSLIB_REV = "1706ae68b63996f1d97717e672e50c9e3933d933"
PHYSLIB_URL = "https://github.com/leanprover-community/physlib"
LEGACY_PHYSLEAN_URL = "https://github.com/HEPLean/PhysLean"
DERIVE_POLICY = "derive_inline_from_problem_only_material"

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

EXPECTED_IMAGES: tuple[str, ...] = (
    "E1_page-9.png",
    "E1_page-11.png",
    "E1_page-12.png",
    "E1_page-13.png",
    "E1_page-14.png",
    "T1_page-1.png",
    "T1_page-2.png",
    "T1_page-3.png",
    "T2_page-1.png",
    "T2_page-2.png",
    "T2_page-3.png",
    "T2_page-4.png",
    "T3_page-1.png",
    "T3_page-2.png",
    "T3_page-3.png",
    "T3_page-4.png",
)
EXPECTED_PROBLEM_PDFS: tuple[str, ...] = tuple(
    f"raw/{paper}_problem.pdf" for paper in ("T1", "T2", "T3", "E1")
)
THEORY_GENERAL_PDF = "raw/theory_general_instructions.pdf"

LAKE_INPUT_FILES = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
NORMALIZED_LAKEFILE = f"""name = \"ipho_2026_run\"
version = \"0.1.0\"
keywords = [\"physics\"]
defaultTargets = [\"IPhO2026Run\"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = \"mathlib\"
scope = \"leanprover-community\"
rev = \"v4.31.0\"

[[require]]
name = \"Physlib\"
git = \"{PHYSLIB_URL}\"
rev = \"{PHYSLIB_REV}\"

[[lean_lib]]
name = \"IPhO2026Problems\"

[[lean_lib]]
name = \"IPhO2026Run\"
""".replace('\\"', '"').encode("utf-8")
GENERATED_LAKE_FILES: Mapping[str, bytes] = {
    "IPhO2026Problems.lean": (
        "/-! Empty answer-blind IPhO problem umbrella.\n\n"
        "The trusted controller may replace this file after it creates only "
        "the authorized target modules. -/\n"
    ).encode("utf-8"),
    "IPhO2026Run.lean": (
        "import IPhO2026Problems\n\n"
        "/-! Minimal answer-blind IPhO 2026 Lake entry point. -/\n"
    ).encode("utf-8"),
}

BLIND_ROW_KEYS = {
    "schema_version",
    "protocol",
    "evaluation_mode",
    "official_answer_seen",
    "phase",
    "id",
    "index",
    "source_index",
    "problem_id",
    "part_id",
    "question",
    "current_question",
    "shared_context",
    "category",
    "dataset",
    "dataset_format",
    "paper",
    "kind",
    "formalization_ready",
    "image",
    "images",
    "previous_parts",
    "source_page",
    "printed_page",
    "problem_assets",
}
BLIND_MANIFEST_KEYS = {
    "schema_version",
    "protocol",
    "phase",
    "evaluation_mode",
    "official_answer_seen",
    "row_count",
    "blind_output",
    "blind_sha256",
    "targets",
}

FORBIDDEN_KEY_STEMS = {
    "answer",
    "answers",
    "explanation",
    "grader",
    "marking",
    "reasoning",
    "rubric",
    "solution",
    "solutions",
}
FORBIDDEN_DIRECTORIES = {
    ".git",
    ".hg",
    ".svn",
    "blueprint",
    "blueprints",
    "reports",
    "references",
}
FORBIDDEN_FILE_TOKENS = {
    "answer",
    "grader",
    "marking",
    "report",
    "solution",
}
SECRET_PATTERNS = (
    re.compile(r"-----BEGIN [A-Z0-9 ]*PRIVATE KEY-----"),
    re.compile(r"sk-ant-[A-Za-z0-9_-]{16,}"),
    re.compile(r"sk-proj-[A-Za-z0-9_-]{16,}"),
    re.compile(r"sk-[A-Za-z0-9]{40,}"),
    re.compile(r"github_pat_[A-Za-z0-9_]{32,}"),
    re.compile(r"gh[pousr]_[A-Za-z0-9]{20,}"),
    re.compile(r"(?:AKIA|ASIA)[0-9A-Z]{16}"),
)
ABSOLUTE_PATH = re.compile(
    r"(?:(?<=^)|(?<=[\s'\"=:(]))/(?:etc|home|mnt|opt|private|root|srv|tmp|usr|var)(?:/|\b)",
    re.MULTILINE,
)
WINDOWS_PATH = re.compile(r"(?i)(?:(?<=^)|(?<=[\s'\"=(]))[A-Z]:[\\/]", re.MULTILINE)
SHA256 = re.compile(r"[0-9a-f]{64}")
GIT_COMMIT = re.compile(r"[0-9a-f]{40}")


class IsolationError(ValueError):
    """An input or output violates the answer-blind seed boundary."""


class PayloadFile(NamedTuple):
    destination: str
    data: bytes
    group: str


class BlindContract(NamedTuple):
    target_ids: tuple[str, ...]
    asset_hashes: dict[str, str]
    row_count: int
    bundle_hash: str
    manifest_hash: str


def _json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def _pretty_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    ).encode("utf-8")


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _hash_index(index: Mapping[str, str]) -> str:
    return _sha256(_json_bytes(dict(sorted(index.items()))))


def _field_tokens(value: object) -> list[str]:
    text = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", str(value))
    return [part.casefold() for part in re.split(r"[^A-Za-z0-9]+", text) if part]


def _audit_text(text: str, *, location: str) -> None:
    if ABSOLUTE_PATH.search(text) or WINDOWS_PATH.search(text):
        raise IsolationError(f"{location}: absolute filesystem path is forbidden")
    for pattern in SECRET_PATTERNS:
        if pattern.search(text):
            raise IsolationError(f"{location}: credential-like text is forbidden")


def _audit_structured(value: Any, *, location: str = "$") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            child_location = f"{location}.{key}"
            tokens = _field_tokens(key)
            if str(key) == "official_answer_seen":
                if child is not False:
                    raise IsolationError(
                        f"{child_location}: answer-blind integrity flag must be false"
                    )
            elif str(key) == "filesystem_answer_blind":
                if child is not True:
                    raise IsolationError(
                        f"{child_location}: filesystem isolation must be asserted"
                    )
            elif str(key) == "network_answer_blind":
                if child is not False:
                    raise IsolationError(
                        f"{child_location}: network blindness must not be claimed"
                    )
            elif any(token in FORBIDDEN_KEY_STEMS for token in tokens) or (
                "reusable" in tokens and "conclusions" in tokens
            ):
                raise IsolationError(f"{child_location}: forbidden controller field")
            if any(
                token in {"token", "secret", "password", "credential"}
                for token in tokens
            ):
                raise IsolationError(f"{child_location}: forbidden credential field")
            _audit_structured(child, location=child_location)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _audit_structured(child, location=f"{location}[{index}]")
    elif isinstance(value, str):
        normalized = value.casefold().replace("\\", "/")
        path_like = "/" in normalized or normalized.endswith(
            (".json", ".jsonl", ".pdf", ".png", ".txt", ".lean")
        )
        if path_like and re.search(
            r"(?:^|[/_. -])(solutions?|marking|grader|answer[-_ ]?page)(?:[/_. -]|$)",
            normalized,
        ):
            raise IsolationError(f"{location}: forbidden controller asset reference")
        _audit_text(value, location=location)


def _safe_relative(raw: object, *, label: str) -> str:
    value = str(raw)
    if not value or "\\" in value or "\x00" in value:
        raise IsolationError(f"{label} is not a safe project-relative path")
    path = PurePosixPath(value)
    if (
        path.is_absolute()
        or path.as_posix() != value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise IsolationError(
            f"{label} is not a normalized project-relative path: {value!r}"
        )
    folded = [part.casefold() for part in path.parts]
    if any(part in FORBIDDEN_DIRECTORIES for part in folded):
        raise IsolationError(f"{label} contains a forbidden directory: {value}")
    for part in folded:
        tokens = {
            token for token in re.split(r"[-_.]+", PurePosixPath(part).stem) if token
        }
        if tokens.intersection(FORBIDDEN_FILE_TOKENS):
            raise IsolationError(f"{label} contains a forbidden filename: {value}")
        if part.startswith("problem_ipho_2026_") and part.endswith(".lean"):
            raise IsolationError(f"old IPhO Lean target is forbidden: {value}")
    return path.as_posix()


def _plain_directory(path: Path, *, label: str) -> Path:
    if path.is_symlink():
        raise IsolationError(f"{label} must not be a symbolic link: {path}")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise IsolationError(f"{label} does not exist: {path}") from exc
    if not resolved.is_dir():
        raise IsolationError(f"{label} is not a directory: {path}")
    return resolved


def _plain_file(path: Path, *, label: str) -> bytes:
    if path.is_symlink() or not path.is_file():
        raise IsolationError(f"{label} must be a plain regular file: {path}")
    return path.read_bytes()


def _asset_file(root: Path, relative: str) -> bytes:
    normalized = _safe_relative(relative, label="problem asset path")
    candidate = root.joinpath(*PurePosixPath(normalized).parts)
    if candidate.is_symlink():
        raise IsolationError(f"problem asset must not be a symbolic link: {relative}")
    try:
        resolved = candidate.resolve(strict=True)
    except FileNotFoundError as exc:
        raise IsolationError(f"problem asset does not exist: {relative}") from exc
    except OSError as exc:
        raise IsolationError(f"problem asset cannot be resolved: {relative}") from exc
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise IsolationError(f"problem asset escapes asset root: {relative}") from exc
    if not resolved.is_file():
        raise IsolationError(f"problem asset is not a regular file: {relative}")
    return resolved.read_bytes()


def _read_json_object(data: bytes, *, location: str) -> dict[str, Any]:
    try:
        value = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise IsolationError(f"{location}: invalid UTF-8 JSON") from exc
    if not isinstance(value, dict):
        raise IsolationError(f"{location}: expected a JSON object")
    _audit_structured(value, location=location)
    return value


def _read_jsonl(data: bytes, *, location: str) -> list[dict[str, Any]]:
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise IsolationError(f"{location}: expected UTF-8 JSONL") from exc
    _audit_text(text, location=location)
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise IsolationError(f"{location}:{line_number}: invalid JSON") from exc
        if not isinstance(row, dict):
            raise IsolationError(f"{location}:{line_number}: row must be an object")
        _audit_structured(row, location=f"{location}:{line_number}")
        rows.append(row)
    return rows


def _nonempty_string(value: object, *, location: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise IsolationError(f"{location}: expected a non-empty string")
    return value.strip()


def _parse_blind_rows(data: bytes, *, location: str) -> BlindContract:
    rows = _read_jsonl(data, location=location)
    if len(rows) != len(EXPECTED_TARGETS):
        raise IsolationError(f"{location}: expected exactly 28 rows, found {len(rows)}")

    assets: dict[str, str] = {}
    observed_images: set[str] = set()
    target_ids: list[str] = []
    for position, (row, expected) in enumerate(zip(rows, EXPECTED_TARGETS), 1):
        if set(row) != BLIND_ROW_KEYS:
            raise IsolationError(
                f"{location}:{position}: unexpected blind row fields "
                f"{sorted(set(row).symmetric_difference(BLIND_ROW_KEYS))}"
            )
        expected_id, expected_index, paper = expected
        if (row.get("id"), row.get("index"), row.get("paper")) != expected:
            raise IsolationError(
                f"{location}:{position}: target inventory mismatch; expected {expected!r}"
            )
        if (
            row.get("schema_version") != SCHEMA_VERSION
            or row.get("protocol") != BLIND_PROTOCOL
            or row.get("evaluation_mode") != "answer_blind"
            or row.get("official_answer_seen") is not False
            or row.get("phase") != "solve"
            or row.get("formalization_ready") is not True
        ):
            raise IsolationError(
                f"{location}:{position}: invalid answer-blind solve state"
            )
        if row.get("problem_id") != f"ipho_2026_{paper.casefold()}":
            raise IsolationError(
                f"{location}:{position}: problem_id does not match paper"
            )
        for key in (
            "source_index",
            "part_id",
            "question",
            "current_question",
            "shared_context",
            "category",
            "dataset",
            "dataset_format",
            "kind",
        ):
            _nonempty_string(row.get(key), location=f"{location}:{position}.{key}")
        if not isinstance(row.get("source_page"), int) or row["source_page"] < 0:
            raise IsolationError(f"{location}:{position}: invalid source_page")
        if not isinstance(row.get("printed_page"), int) or row["printed_page"] < 0:
            raise IsolationError(f"{location}:{position}: invalid printed_page")

        previous_parts = row.get("previous_parts")
        if not isinstance(previous_parts, list):
            raise IsolationError(
                f"{location}:{position}: previous_parts must be a list"
            )
        for prior_index, prior in enumerate(previous_parts):
            if not isinstance(prior, dict) or set(prior) != {
                "source_id",
                "part_id",
                "question",
                "dependency_policy",
            }:
                raise IsolationError(
                    f"{location}:{position}.previous_parts[{prior_index}]: invalid fields"
                )
            for key in ("source_id", "part_id", "question"):
                _nonempty_string(
                    prior.get(key),
                    location=f"{location}:{position}.previous_parts[{prior_index}].{key}",
                )
            if prior.get("dependency_policy") != DERIVE_POLICY:
                raise IsolationError(
                    f"{location}:{position}.previous_parts[{prior_index}]: unsafe dependency policy"
                )

        images = row.get("images")
        if not isinstance(images, list) or not images or row.get("image") != images[0]:
            raise IsolationError(f"{location}:{position}: invalid problem image list")
        normalized_images: list[str] = []
        for raw_image in images:
            name = _safe_relative(raw_image, label="problem image name")
            if len(PurePosixPath(name).parts) != 1 or not re.fullmatch(
                rf"{paper}_page-[1-9][0-9]*\.png", name
            ):
                raise IsolationError(
                    f"{location}:{position}: invalid {paper} image {name}"
                )
            normalized_images.append(name)
            observed_images.add(name)
        if len(set(normalized_images)) != len(normalized_images):
            raise IsolationError(f"{location}:{position}: duplicate problem image")

        raw_assets = row.get("problem_assets")
        if not isinstance(raw_assets, list):
            raise IsolationError(
                f"{location}:{position}: problem_assets must be a list"
            )
        row_assets: dict[str, tuple[str, str]] = {}
        for asset_index, raw_asset in enumerate(raw_assets):
            if not isinstance(raw_asset, dict) or set(raw_asset) != {
                "kind",
                "path",
                "sha256",
            }:
                raise IsolationError(
                    f"{location}:{position}.problem_assets[{asset_index}]: invalid fields"
                )
            kind = raw_asset.get("kind")
            path = _safe_relative(raw_asset.get("path"), label="problem asset path")
            digest = raw_asset.get("sha256")
            if (
                kind
                not in {
                    "problem_pdf",
                    "problem_page",
                    "problem_general_instructions",
                }
                or not isinstance(digest, str)
                or SHA256.fullmatch(digest) is None
            ):
                raise IsolationError(
                    f"{location}:{position}.problem_assets[{asset_index}]: invalid asset"
                )
            if path in row_assets:
                raise IsolationError(
                    f"{location}:{position}: duplicate problem asset {path}"
                )
            row_assets[path] = (str(kind), digest)
            prior_digest = assets.setdefault(path, digest)
            if prior_digest != digest:
                raise IsolationError(
                    f"{location}:{position}: inconsistent hash for {path}"
                )

        expected_pdf = f"raw/{paper}_problem.pdf"
        expected_row_assets = {expected_pdf: "problem_pdf"} | {
            f"image/{name}": "problem_page" for name in normalized_images
        }
        if paper != "E1":
            expected_row_assets[THEORY_GENERAL_PDF] = "problem_general_instructions"
        if {
            path: kind for path, (kind, _digest) in row_assets.items()
        } != expected_row_assets:
            raise IsolationError(
                f"{location}:{position}: asset declarations do not match images"
            )
        target_ids.append(expected_id)

    if set(observed_images) != set(EXPECTED_IMAGES):
        missing = sorted(set(EXPECTED_IMAGES) - observed_images)
        extra = sorted(observed_images - set(EXPECTED_IMAGES))
        raise IsolationError(
            f"problem page inventory mismatch (missing={missing}, extra={extra})"
        )
    expected_assets = (
        set(EXPECTED_PROBLEM_PDFS)
        | {f"image/{name}" for name in EXPECTED_IMAGES}
        | {THEORY_GENERAL_PDF}
    )
    if set(assets) != expected_assets:
        raise IsolationError(
            "blind rows do not bind exactly 4 problem PDFs, 16 page PNGs, "
            "and the theory general-instructions PDF"
        )
    return BlindContract(
        tuple(target_ids), dict(sorted(assets.items())), len(rows), _sha256(data), ""
    )


def _load_blind_contract(
    questions_only: Path, blind_manifest: Path
) -> tuple[bytes, BlindContract]:
    bundle_data = _plain_file(questions_only, label="questions-only JSONL")
    manifest_data = _plain_file(blind_manifest, label="blind manifest")
    contract = _parse_blind_rows(bundle_data, location=BUNDLE_DESTINATION)
    manifest = _read_json_object(manifest_data, location="blind manifest")
    if set(manifest) != BLIND_MANIFEST_KEYS:
        raise IsolationError("blind manifest has unexpected fields")
    if (
        manifest.get("schema_version") != SCHEMA_VERSION
        or manifest.get("protocol") != BLIND_PROTOCOL
        or manifest.get("phase") != "solve"
        or manifest.get("evaluation_mode") != "answer_blind"
        or manifest.get("official_answer_seen") is not False
        or manifest.get("row_count") != len(EXPECTED_TARGETS)
        or manifest.get("blind_output") != questions_only.name
        or manifest.get("blind_sha256") != contract.bundle_hash
    ):
        raise IsolationError("blind manifest does not bind this answer-blind bundle")
    targets = manifest.get("targets")
    if not isinstance(targets, list) or len(targets) != len(EXPECTED_TARGETS):
        raise IsolationError("blind manifest target inventory is invalid")
    rows = _read_jsonl(bundle_data, location=BUNDLE_DESTINATION)
    for position, (target, expected, row) in enumerate(
        zip(targets, EXPECTED_TARGETS, rows), 1
    ):
        if not isinstance(target, dict) or set(target) != {
            "id",
            "index",
            "paper",
            "blind_record_sha256",
        }:
            raise IsolationError(f"blind manifest target {position} has invalid fields")
        if (target.get("id"), target.get("index"), target.get("paper")) != expected:
            raise IsolationError(f"blind manifest target {position} is out of scope")
        if target.get("blind_record_sha256") != _sha256(_json_bytes(row)):
            raise IsolationError(f"blind manifest target {position} row hash mismatch")
    return bundle_data, contract._replace(manifest_hash=_sha256(manifest_data))


def _validate_lake_files(lake_root: Path) -> list[PayloadFile]:
    root = _plain_directory(lake_root, label="Lake skeleton root")
    data = {
        name: _plain_file(root / name, label=f"Lake skeleton {name}")
        for name in LAKE_INPUT_FILES
    }
    try:
        toolchain = data["lean-toolchain"].decode("utf-8").strip()
    except UnicodeDecodeError as exc:
        raise IsolationError("lean-toolchain is not UTF-8") from exc
    if toolchain != LEAN_VERSION:
        raise IsolationError(f"solver seed requires exactly {LEAN_VERSION}")

    try:
        lakefile = tomllib.loads(data["lakefile.toml"].decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise IsolationError("invalid UTF-8 lakefile.toml") from exc
    _audit_structured(lakefile, location="lakefile.toml")
    if lakefile.get("name") != "ipho_2026_run" or lakefile.get("defaultTargets") != [
        "IPhO2026Run"
    ]:
        raise IsolationError("lakefile.toml is not the clean IPhO 2026 skeleton")
    requirements = lakefile.get("require")
    if not isinstance(requirements, list) or len(requirements) != 2:
        raise IsolationError(
            "lakefile.toml must have exactly Mathlib and one approved physics dependency"
        )
    requirement_by_name = {
        item.get("name"): item for item in requirements if isinstance(item, dict)
    }
    physics_names = set(requirement_by_name) - {"mathlib"}
    if (
        set(requirement_by_name) - physics_names != {"mathlib"}
        or len(physics_names) != 1
    ):
        raise IsolationError("lakefile.toml dependency set is not answer-blind physics")
    physics_name = next(iter(physics_names))
    if physics_name not in {"PhysLean", "Physlib"}:
        raise IsolationError("lakefile.toml has an unsupported physics dependency")
    if (
        requirement_by_name["mathlib"].get("rev") != "v4.31.0"
        or requirement_by_name["mathlib"].get("scope") != "leanprover-community"
    ):
        raise IsolationError("lakefile.toml must pin Mathlib v4.31.0")
    physics = requirement_by_name[physics_name]
    expected_physics_url = (
        LEGACY_PHYSLEAN_URL if physics_name == "PhysLean" else PHYSLIB_URL
    )
    if physics.get("rev") != PHYSLIB_REV or physics.get("git") != expected_physics_url:
        raise IsolationError("lakefile.toml must pin the approved physics revision")
    lean_libs = lakefile.get("lean_lib")
    approved_lean_libs = (
        [{"name": "IPhO2026Run"}],
        [{"name": "IPhO2026Problems"}, {"name": "IPhO2026Run"}],
    )
    if not isinstance(lean_libs, list) or lean_libs not in approved_lean_libs:
        raise IsolationError(
            "lakefile.toml must expose only IPhO2026Problems and IPhO2026Run"
        )

    manifest = _read_json_object(
        data["lake-manifest.json"], location="lake-manifest.json"
    )
    if (
        manifest.get("packagesDir") != ".lake/packages"
        or manifest.get("lakeDir") != ".lake"
        or manifest.get("name") != "ipho_2026_run"
        or not isinstance(manifest.get("packages"), list)
    ):
        raise IsolationError("lake-manifest.json is not a clean IPhO manifest")
    packages: dict[str, dict[str, Any]] = {}
    for position, package in enumerate(manifest["packages"]):
        if not isinstance(package, dict):
            raise IsolationError(f"lake-manifest package {position} is not an object")
        name = package.get("name")
        url = package.get("url")
        rev = package.get("rev")
        if (
            not isinstance(name, str)
            or name in packages
            or package.get("type") != "git"
            or not isinstance(url, str)
            or not isinstance(rev, str)
            or GIT_COMMIT.fullmatch(rev) is None
            or package.get("subDir") is not None
        ):
            raise IsolationError(
                f"lake-manifest package {position} is not a pinned Git package"
            )
        parsed = urlsplit(url)
        if (
            parsed.scheme != "https"
            or parsed.hostname != "github.com"
            or parsed.username
        ):
            raise IsolationError(f"lake-manifest package {name} has an unsafe URL")
        packages[name] = package
    if packages.get("mathlib", {}).get("rev") != MATHLIB_REV:
        raise IsolationError("lake-manifest.json has the wrong Mathlib revision")
    physics_package_names = {"PhysLean", "Physlib"}.intersection(packages)
    if len(physics_package_names) != 1:
        raise IsolationError("lake-manifest.json must contain one physics package")
    manifest_physics_name = next(iter(physics_package_names))
    manifest_physics = packages[manifest_physics_name]
    expected_manifest_url = (
        LEGACY_PHYSLEAN_URL if manifest_physics_name == "PhysLean" else PHYSLIB_URL
    )
    if (
        manifest_physics.get("rev") != PHYSLIB_REV
        or manifest_physics.get("url") != expected_manifest_url
    ):
        raise IsolationError("lake-manifest.json has the wrong physics package pin")

    normalized_manifest = json.loads(json.dumps(manifest))
    for package in normalized_manifest["packages"]:
        if package.get("name") == manifest_physics_name:
            package["name"] = "Physlib"
            package["url"] = PHYSLIB_URL
            if "inputRev" in package:
                package["inputRev"] = PHYSLIB_REV
            break
    normalized_data = {
        "lakefile.toml": NORMALIZED_LAKEFILE,
        "lake-manifest.json": _pretty_json_bytes(normalized_manifest),
        "lean-toolchain": (LEAN_VERSION + "\n").encode("utf-8"),
    }
    payload: list[PayloadFile] = []
    for name in LAKE_INPUT_FILES:
        _audit_text(normalized_data[name].decode("utf-8"), location=name)
        payload.append(PayloadFile(name, normalized_data[name], "lake_skeleton"))
    for name, generated in sorted(GENERATED_LAKE_FILES.items()):
        _audit_text(generated.decode("utf-8"), location=name)
        payload.append(PayloadFile(name, generated, "lake_skeleton"))
    return payload


def _build_payload(
    *,
    questions_only: Path,
    blind_manifest: Path,
    asset_root: Path,
    lake_root: Path,
) -> tuple[list[PayloadFile], BlindContract]:
    bundle_data, contract = _load_blind_contract(questions_only, blind_manifest)
    assets_root = _plain_directory(asset_root, label="safe asset root")
    payload = _validate_lake_files(lake_root)
    payload.append(PayloadFile(BUNDLE_DESTINATION, bundle_data, "blind_bundle"))
    for relative, expected_digest in contract.asset_hashes.items():
        data = _asset_file(assets_root, relative)
        if _sha256(data) != expected_digest:
            raise IsolationError(f"problem asset hash mismatch: {relative}")
        payload.append(
            PayloadFile(
                _safe_relative(
                    f"{ASSET_DESTINATION_ROOT}/{relative}",
                    label="seed asset destination",
                ),
                data,
                "asset",
            )
        )
    seen: set[str] = set()
    for item in payload:
        destination = _safe_relative(item.destination, label="seed destination")
        if destination in seen:
            raise IsolationError(f"duplicate seed destination: {destination}")
        seen.add(destination)
    return sorted(payload, key=lambda item: item.destination), contract


def _manifest_for(
    payload: Sequence[PayloadFile], contract: BlindContract
) -> dict[str, Any]:
    groups: dict[str, dict[str, str]] = {
        "lake_skeleton": {},
        "asset": {},
        "blind_bundle": {},
    }
    payload_files: dict[str, str] = {}
    bundle_size = 0
    for item in payload:
        digest = _sha256(item.data)
        groups[item.group][item.destination] = digest
        payload_files[item.destination] = digest
        if item.group == "blind_bundle":
            bundle_size = len(item.data)
    lake = dict(sorted(groups["lake_skeleton"].items()))
    assets = dict(sorted(groups["asset"].items()))
    bundle_hash = groups["blind_bundle"].get(BUNDLE_DESTINATION)
    if bundle_hash != contract.bundle_hash:
        raise IsolationError("internal blind bundle hash mismatch")
    engine: dict[str, str] = {}
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "source_revision_disclosed": False,
        "engine_files": engine,
        "engine_files_sha256": _hash_index(engine),
        "lake_skeleton_files": lake,
        "lake_skeleton_sha256": _hash_index(lake),
        "blind_bundle": {
            "path": BUNDLE_DESTINATION,
            "row_count": contract.row_count,
            "sha256": contract.bundle_hash,
            "size": bundle_size,
        },
        "blind_bundle_sha256": contract.bundle_hash,
        "blind_source_manifest_sha256": contract.manifest_hash,
        "target_ids": list(contract.target_ids),
        "target_ids_sha256": _sha256(_json_bytes(list(contract.target_ids))),
        "assets": assets,
        "assets_sha256": _hash_index(assets),
        "payload_files": dict(sorted(payload_files.items())),
        "payload_sha256": _hash_index(payload_files),
        "isolation_claims": {"filesystem": True, "network": False},
        "isolation": {
            "filesystem_answer_blind": True,
            "network_answer_blind": False,
        },
        "workspace_policy": {
            "fresh_git_init": True,
            "history": False,
            "remotes": [],
            "solver_labels": ["GPT", "K3"],
        },
    }
    _audit_structured(manifest, location="isolation manifest")
    return manifest


def _regular_files(root: Path) -> list[Path]:
    result: list[Path] = []

    def walk(directory: Path) -> None:
        for entry in sorted(os.scandir(directory), key=lambda item: item.name):
            path = Path(entry.path)
            relative = path.relative_to(root).as_posix()
            _safe_relative(relative, label="seed path")
            if entry.is_symlink():
                raise IsolationError(f"seed contains a symbolic link: {relative}")
            if entry.is_dir(follow_symlinks=False):
                walk(path)
            elif entry.is_file(follow_symlinks=False):
                result.append(path)
            else:
                raise IsolationError(
                    f"seed contains unsupported filesystem entry: {relative}"
                )

    walk(root)
    return result


def _hash_map(value: object, *, field: str) -> dict[str, str]:
    if not isinstance(value, dict):
        raise IsolationError(f"manifest.{field} must be an object")
    result: dict[str, str] = {}
    for raw_path, raw_digest in value.items():
        path = _safe_relative(raw_path, label=f"manifest.{field} path")
        if not isinstance(raw_digest, str) or SHA256.fullmatch(raw_digest) is None:
            raise IsolationError(f"manifest.{field}[{path!r}] is not a SHA-256")
        result[path] = raw_digest
    return result


def validate_seed(seed_root: Path | str) -> dict[str, Any]:
    """Recursively verify a materialized IPhO problem-only seed."""

    root = _plain_directory(Path(seed_root), label="seed root")
    manifest_path = root / MANIFEST_NAME
    manifest_data = _plain_file(manifest_path, label=MANIFEST_NAME)
    manifest = _read_json_object(manifest_data, location=MANIFEST_NAME)
    if (
        manifest.get("schema_version") != SCHEMA_VERSION
        or manifest.get("protocol") != PROTOCOL
    ):
        raise IsolationError("unsupported isolation manifest schema/protocol")
    if (
        manifest.get("source_revision_disclosed") is not False
        or "source_commit" in manifest
    ):
        raise IsolationError("seed must not disclose source history")
    if manifest.get("engine_files") != {}:
        raise IsolationError("solver seed must not contain editable runtime code")
    if manifest.get("isolation_claims") != {"filesystem": True, "network": False}:
        raise IsolationError("invalid legacy isolation claims")
    if manifest.get("isolation") != {
        "filesystem_answer_blind": True,
        "network_answer_blind": False,
    }:
        raise IsolationError("invalid explicit isolation claims")
    if manifest.get("workspace_policy") != {
        "fresh_git_init": True,
        "history": False,
        "remotes": [],
        "solver_labels": ["GPT", "K3"],
    }:
        raise IsolationError("invalid fresh Git workspace policy")

    engine = _hash_map(manifest.get("engine_files"), field="engine_files")
    lake = _hash_map(manifest.get("lake_skeleton_files"), field="lake_skeleton_files")
    assets = _hash_map(manifest.get("assets"), field="assets")
    payload = _hash_map(manifest.get("payload_files"), field="payload_files")
    required_lake = set(LAKE_INPUT_FILES) | set(GENERATED_LAKE_FILES)
    if set(lake) != required_lake:
        raise IsolationError("seed Lake skeleton is not the exact clean allowlist")
    if manifest.get("engine_files_sha256") != _hash_index(engine):
        raise IsolationError("engine index hash mismatch")
    if manifest.get("lake_skeleton_sha256") != _hash_index(lake):
        raise IsolationError("Lake skeleton index hash mismatch")
    if manifest.get("assets_sha256") != _hash_index(assets):
        raise IsolationError("asset index hash mismatch")
    if manifest.get("payload_sha256") != _hash_index(payload):
        raise IsolationError("payload index hash mismatch")

    bundle = manifest.get("blind_bundle")
    if not isinstance(bundle, dict) or bundle.get("path") != BUNDLE_DESTINATION:
        raise IsolationError("invalid blind bundle manifest entry")
    bundle_hash = bundle.get("sha256")
    if not isinstance(bundle_hash, str) or SHA256.fullmatch(bundle_hash) is None:
        raise IsolationError("invalid blind bundle SHA-256")
    if manifest.get("blind_bundle_sha256") != bundle_hash:
        raise IsolationError("blind bundle hash fields disagree")
    source_manifest_hash = manifest.get("blind_source_manifest_sha256")
    if (
        not isinstance(source_manifest_hash, str)
        or SHA256.fullmatch(source_manifest_hash) is None
    ):
        raise IsolationError("invalid blind source manifest SHA-256")

    combined = dict(engine)
    for group in (lake, assets, {BUNDLE_DESTINATION: bundle_hash}):
        if set(combined).intersection(group):
            raise IsolationError("seed manifest file groups overlap")
        combined.update(group)
    if combined != payload:
        raise IsolationError("payload inventory does not equal its file groups")

    actual_files = _regular_files(root)
    actual_relatives = {
        path.relative_to(root).as_posix()
        for path in actual_files
        if path != manifest_path
    }
    if actual_relatives != set(payload):
        raise IsolationError(
            "seed inventory mismatch "
            f"(missing={sorted(set(payload) - actual_relatives)}, "
            f"extra={sorted(actual_relatives - set(payload))})"
        )
    for path in actual_files:
        if path == manifest_path:
            continue
        relative = path.relative_to(root).as_posix()
        if stat.S_IMODE(path.stat().st_mode) & 0o022:
            raise IsolationError(f"seed file is group/world writable: {relative}")
        data = path.read_bytes()
        if _sha256(data) != payload[relative]:
            raise IsolationError(f"seed file hash mismatch: {relative}")
        suffix = path.suffix.casefold()
        if suffix not in {".pdf", ".png"}:
            try:
                _audit_text(data.decode("utf-8"), location=relative)
            except UnicodeDecodeError as exc:
                raise IsolationError(f"{relative}: expected UTF-8 text") from exc
    for relative, expected in GENERATED_LAKE_FILES.items():
        if (root / relative).read_bytes() != expected:
            raise IsolationError(f"generated empty umbrella was modified: {relative}")
    normalized_lake_payload = _validate_lake_files(root)
    for item in normalized_lake_payload:
        if (
            item.destination in LAKE_INPUT_FILES
            and (root / item.destination).read_bytes() != item.data
        ):
            raise IsolationError(
                f"seed Lake file is not in normalized Physlib form: {item.destination}"
            )

    bundle_path = root / BUNDLE_DESTINATION
    bundle_data = bundle_path.read_bytes()
    contract = _parse_blind_rows(bundle_data, location=BUNDLE_DESTINATION)
    if contract.bundle_hash != bundle_hash:
        raise IsolationError("blind bundle content hash mismatch")
    if bundle.get("row_count") != contract.row_count or bundle.get("size") != len(
        bundle_data
    ):
        raise IsolationError("blind bundle metadata mismatch")
    if manifest.get("target_ids") != list(contract.target_ids) or manifest.get(
        "target_ids_sha256"
    ) != _sha256(_json_bytes(list(contract.target_ids))):
        raise IsolationError("target inventory does not match blind bundle")
    expected_assets = {
        f"{ASSET_DESTINATION_ROOT}/{relative}": digest
        for relative, digest in contract.asset_hashes.items()
    }
    if assets != dict(sorted(expected_assets.items())):
        raise IsolationError("seed assets exceed the fixed problem-only allowlist")
    return manifest


def _ensure_new_destination(path: Path) -> Path:
    if path.exists() or path.is_symlink():
        raise IsolationError(f"seed output must be a new path: {path}")
    absolute = path.absolute()
    try:
        parent = absolute.parent.resolve(strict=True)
    except OSError as exc:
        raise IsolationError(
            f"seed output parent does not exist: {path.parent}"
        ) from exc
    if parent != absolute.parent or not parent.is_dir():
        raise IsolationError(
            "seed output parent must be a plain directory without symlinks"
        )
    return absolute


def _write_atomic(
    destination: Path, payload: Sequence[PayloadFile], manifest: Mapping[str, Any]
) -> None:
    target = _ensure_new_destination(destination)
    staging = Path(
        tempfile.mkdtemp(prefix=f".{target.name}.staging-", dir=target.parent)
    )
    try:
        for item in payload:
            path = staging.joinpath(*PurePosixPath(item.destination).parts)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(item.data)
            path.chmod(0o644)
        (staging / MANIFEST_NAME).write_bytes(_pretty_json_bytes(manifest))
        (staging / MANIFEST_NAME).chmod(0o644)
        validate_seed(staging)
        os.replace(staging, target)
        directory_fd = os.open(target.parent, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise


def build_seed(
    *,
    questions_only: Path,
    blind_manifest: Path,
    asset_root: Path,
    lake_root: Path,
    output_dir: Path | None = None,
    dry_run: bool = False,
) -> dict[str, Any]:
    """Validate inputs and optionally atomically materialize the seed."""

    payload, contract = _build_payload(
        questions_only=Path(questions_only),
        blind_manifest=Path(blind_manifest),
        asset_root=Path(asset_root),
        lake_root=Path(lake_root),
    )
    manifest = _manifest_for(payload, contract)
    if dry_run:
        return manifest
    if output_dir is None:
        raise IsolationError("output_dir is required unless dry_run=True")
    _write_atomic(Path(output_dir), payload, manifest)
    return manifest


def build_solver_seed(**kwargs: Any) -> dict[str, Any]:
    """Stable descriptive alias for controller callers."""

    return build_seed(**kwargs)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--questions-only", type=Path)
    parser.add_argument("--blind-manifest", type=Path)
    parser.add_argument("--asset-root", type=Path)
    parser.add_argument("--lake-root", type=Path)
    parser.add_argument("--output", dest="output_dir", type=Path)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--validate-seed", type=Path)
    return parser


def _required(parser: argparse.ArgumentParser, value: Any, flag: str) -> Any:
    if value is None:
        parser.error(f"{flag} is required in build mode")
    return value


def main(argv: Iterable[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    if args.validate_seed is not None:
        manifest = validate_seed(args.validate_seed)
    else:
        if not args.dry_run and args.output_dir is None:
            parser.error("--output is required unless --dry-run is used")
        manifest = build_seed(
            questions_only=_required(parser, args.questions_only, "--questions-only"),
            blind_manifest=_required(parser, args.blind_manifest, "--blind-manifest"),
            asset_root=_required(parser, args.asset_root, "--asset-root"),
            lake_root=_required(parser, args.lake_root, "--lake-root"),
            output_dir=args.output_dir,
            dry_run=args.dry_run,
        )
    print(json.dumps(manifest, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
