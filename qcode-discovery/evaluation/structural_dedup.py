"""Structural novelty gate for CSS bivariate-bicycle codes.

BLISS supplies a colored-Tanner-graph canonical form and a candidate
isomorphism.  A match is accepted only after replaying the full qubit and
X/Z-check permutations directly against both parity-check matrices.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.metadata
import json
import math
import multiprocessing
import os
import platform
import signal
import tempfile
import threading
import time
from collections import deque
from contextlib import contextmanager
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Mapping

import numpy as np

from evaluation.bb_code import build_bb_code, get_code_params_fast, validate_terms
from evaluation.distance_milp import symplectic_weight_witness
from evaluation.geometry import candidate_geometry, normalize_geometry
from evaluation.tanner_equivalence import (
    canonical_hash,
    extract_full_vertex_isomorphism,
)


KNOWN_CSS_REFERENCES = (
    ("Bravyi [[72,12,6]]", 6, 6,
     [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
    ("Bravyi [[90,8,10]]", 15, 3,
     [(9, 0), (0, 1), (0, 2)], [(0, 0), (2, 0), (7, 0)]),
    ("Bravyi [[108,8,10]]", 9, 6,
     [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
    ("Gross [[144,12,12]]", 12, 6,
     [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
    ("Bravyi [[288,12,18]]", 12, 12,
     [(3, 0), (0, 2), (0, 7)], [(0, 3), (1, 0), (2, 0)]),
    ("Bravyi [[360,12,<=24]]", 30, 6,
     [(9, 0), (0, 1), (0, 2)], [(0, 3), (25, 0), (26, 0)]),
)

STRUCTURAL_SCREEN_CACHE_SCHEMA_VERSION = 1
STRUCTURAL_PAIR_CACHE_SCHEMA_VERSION = 1
STRUCTURAL_PAIR_REPLAY_FIELD = "within_pool_isomorphism_replay"
STRUCTURAL_SCREEN_HARD_TIMEOUT_SECONDS = 300.0
_STRUCTURAL_SCREEN_PACKAGES = (
    "qldpc",
    "numpy",
    "scipy",
    "sympy",
    "igraph",
    "python-igraph",
)
STRUCTURAL_SCREEN_NATIVE_THREAD_ENV = (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
    "NUMBA_NUM_THREADS",
    "GOTO_NUM_THREADS",
)
_STRUCTURAL_SCREEN_NATIVE_THREAD_VALUE = "1"
_STRUCTURAL_SCREEN_SPAWN_ENV_LOCK = threading.Lock()


class StructuralScreenCacheError(RuntimeError):
    """A durable structural-screen cache entry failed validation."""


class StructuralScreenIncompleteError(RuntimeError):
    """At least one candidate needs a retry before screening is complete."""

    def __init__(self, unresolved: list[dict[str, Any]]):
        self.unresolved = tuple(copy.deepcopy(unresolved))
        super().__init__(
            "structural screening is incomplete for "
            f"{len(self.unresolved)} retryable candidate(s)"
        )


def _canonical_json_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            ensure_ascii=False,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise StructuralScreenCacheError(
            "structural-screen input is not canonical JSON"
        ) from exc


def _sha256_json(value: Any) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _atomic_write_json(path: Path, value: Any) -> None:
    payload = _canonical_json_bytes(value) + b"\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.tmp-",
        dir=path.parent,
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        directory = os.open(
            path.parent,
            os.O_RDONLY | getattr(os, "O_DIRECTORY", 0),
        )
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _normalized_screen_input(result: dict[str, Any]) -> dict[str, Any]:
    """Return the exact mathematical/static input bound by one cache key."""

    if isinstance(result.get("construction"), Mapping):
        try:
            from evaluation.construction import normalize_construction_claim

            normalized_claim = normalize_construction_claim(dict(result))
            construction = (
                normalized_claim.get("construction")
                if isinstance(normalized_claim, Mapping)
                and isinstance(normalized_claim.get("construction"), Mapping)
                else normalized_claim
            )
            if not isinstance(construction, Mapping):
                raise TypeError("normalized construction is not an object")
            reported_n = (
                {"present": True, "value": int(result["n"])}
                if "n" in result
                else {"present": False, "value": None}
            )
            reported_k = (
                {"present": True, "value": int(result["k"])}
                if "k" in result
                else {"present": False, "value": None}
            )
        except (KeyError, TypeError, ValueError, OverflowError) as exc:
            raise StructuralScreenCacheError(
                "candidate has an invalid compact construction"
            ) from exc
        return {
            "construction": copy.deepcopy(dict(construction)),
            "reported_n": reported_n,
            "reported_k": reported_k,
        }

    try:
        ell = int(result["ell"])
        m = int(result["m"])
        a_terms = sorted(
            [list(map(int, term)) for term in result["A_terms"]]
        )
        b_terms = sorted(
            [list(map(int, term)) for term in result["B_terms"]]
        )
        reported_n = (
            {"present": True, "value": int(result["n"])}
            if "n" in result
            else {"present": False, "value": None}
        )
        reported_k = (
            {"present": True, "value": int(result["k"])}
            if "k" in result
            else {"present": False, "value": None}
        )
    except (KeyError, TypeError, ValueError) as exc:
        raise StructuralScreenCacheError(
            "candidate has invalid structural-screen defining fields"
        ) from exc
    normalized = {
        "ell": ell,
        "m": m,
        "A_terms": a_terms,
        "B_terms": b_terms,
        "reported_n": reported_n,
        "reported_k": reported_k,
    }
    geometry = normalize_geometry(ell, m, result.get("geometry"))
    if geometry is not None:
        normalized["geometry"] = geometry
    return normalized


def structural_screen_input_sha256(result: dict[str, Any]) -> str:
    """Return the cache identity for one structural-screen construction."""

    return _sha256_json(_normalized_screen_input(result))


def structural_screen_runtime_fingerprint() -> dict[str, Any]:
    """Bind cached results to code and the numerical/BLISS runtime."""

    module_dir = Path(__file__).resolve().parent
    sources: dict[str, str] = {}
    for name in (
        "structural_dedup.py",
        "bb_code.py",
        "geometry.py",
        "tanner_equivalence.py",
        "construction.py",
        "distance_milp.py",
    ):
        path = module_dir / name
        sources[name] = (
            hashlib.sha256(path.read_bytes()).hexdigest()
            if path.is_file()
            else "unavailable"
        )
    try:
        from evaluation.construction import construction_source_fingerprint

        construction_fingerprint = construction_source_fingerprint()
    except (ImportError, OSError, TypeError, ValueError):
        construction_fingerprint = "unavailable"
    packages: dict[str, str | None] = {}
    for name in _STRUCTURAL_SCREEN_PACKAGES:
        try:
            packages[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            packages[name] = None
    payload = {
        "schema_version": STRUCTURAL_SCREEN_CACHE_SCHEMA_VERSION,
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "machine": platform.machine(),
        "platform": platform.platform(),
        "libc": list(platform.libc_ver()),
        "sources": sources,
        "construction_source_fingerprint": construction_fingerprint,
        "packages": packages,
        "worker_native_thread_environment": {
            name: _STRUCTURAL_SCREEN_NATIVE_THREAD_VALUE
            for name in STRUCTURAL_SCREEN_NATIVE_THREAD_ENV
        },
    }
    return {"payload": payload, "sha256": _sha256_json(payload)}


@contextmanager
def _structural_screen_spawn_environment():
    """Clamp native numeric threads before a spawned interpreter imports NumPy.

    ``multiprocessing`` uses a fresh interpreter for these killable workers.
    Setting the variables inside the worker target is too late because module
    imports may already have initialized BLAS/OpenMP pools.  Hold a process-
    local lock only across ``Process.start()`` so structural-screen spawners
    cannot interleave their temporary overrides, then restore the controller's
    exact environment immediately after the child inherited it.  Unrelated
    code must not launch subprocesses concurrently with this private phase.
    """

    with _STRUCTURAL_SCREEN_SPAWN_ENV_LOCK:
        previous = {
            name: os.environ.get(name)
            for name in STRUCTURAL_SCREEN_NATIVE_THREAD_ENV
        }
        try:
            for name in STRUCTURAL_SCREEN_NATIVE_THREAD_ENV:
                os.environ[name] = _STRUCTURAL_SCREEN_NATIVE_THREAD_VALUE
            yield
        finally:
            for name, value in previous.items():
                if value is None:
                    os.environ.pop(name, None)
                else:
                    os.environ[name] = value


def _require_structural_screen_native_thread_environment() -> None:
    """Fail one retryable worker task if its inherited budget is incomplete."""

    mismatched = {
        name: os.environ.get(name)
        for name in STRUCTURAL_SCREEN_NATIVE_THREAD_ENV
        if os.environ.get(name) != _STRUCTURAL_SCREEN_NATIVE_THREAD_VALUE
    }
    if mismatched:
        raise RuntimeError(
            "structural-screen worker native thread budget is incomplete: "
            f"{sorted(mismatched)}"
        )


def _annotation_payload(result: dict[str, Any]) -> dict[str, Any]:
    annotated = annotate_css_result(result)
    payload = {
        "static_eligibility": copy.deepcopy(
            annotated["static_eligibility"]
        ),
        "structural_novelty": copy.deepcopy(
            annotated["structural_novelty"]
        ),
        "structural_rejection": annotated.get("structural_rejection"),
    }
    _validate_annotation_payload(payload)
    return payload


def _logical_basis_upper_bound_report(code: Any) -> dict[str, Any]:
    witness = symplectic_weight_witness(code)
    payload: dict[str, Any] = {
        "schema_version": 1,
        "kind": "qcode-logical-basis-upper-bound-v1",
        "method": "replayed-minimum-symplectic-basis-row",
        "available": witness is not None,
        "upper_bound": None if witness is None else int(witness["weight"]),
        "witness": None if witness is None else witness,
    }
    return {**payload, "report_sha256": _sha256_json(payload)}


def _validate_logical_basis_upper_bound_report(value: Any) -> None:
    if not isinstance(value, dict) or set(value) != {
        "schema_version", "kind", "method", "available", "upper_bound",
        "witness", "report_sha256",
    }:
        raise StructuralScreenCacheError(
            "logical-basis upper-bound report fields changed"
        )
    unsigned = dict(value)
    digest = unsigned.pop("report_sha256", None)
    if digest != _sha256_json(unsigned):
        raise StructuralScreenCacheError(
            "logical-basis upper-bound report self-hash mismatch"
        )
    if (
        value.get("schema_version") != 1
        or value.get("kind") != "qcode-logical-basis-upper-bound-v1"
        or value.get("method")
        != "replayed-minimum-symplectic-basis-row"
        or not isinstance(value.get("available"), bool)
    ):
        raise StructuralScreenCacheError(
            "logical-basis upper-bound report schema is invalid"
        )
    witness = value.get("witness")
    if value["available"]:
        upper = value.get("upper_bound")
        if (
            isinstance(upper, bool)
            or not isinstance(upper, int)
            or upper < 1
            or not isinstance(witness, dict)
            or set(witness) != {
                "side", "index", "dual_side", "dual_index", "weight",
                "bits",
            }
            or witness.get("weight") != upper
            or witness.get("side") not in {"X", "Z"}
            or witness.get("dual_side")
            != ("Z" if witness.get("side") == "X" else "X")
            or isinstance(witness.get("index"), bool)
            or not isinstance(witness.get("index"), int)
            or witness["index"] < 0
            or isinstance(witness.get("dual_index"), bool)
            or not isinstance(witness.get("dual_index"), int)
            or witness["dual_index"] < 0
            or not isinstance(witness.get("bits"), list)
            or not witness["bits"]
            or any(type(bit) is not int or bit not in {0, 1} for bit in witness["bits"])
            or sum(witness["bits"]) != upper
        ):
            raise StructuralScreenCacheError(
                "logical-basis upper-bound witness is invalid"
            )
    elif value.get("upper_bound") is not None or witness is not None:
        raise StructuralScreenCacheError(
            "unavailable logical-basis report carries a witness"
        )


def _validate_annotation_payload(payload: Any) -> None:
    if not isinstance(payload, dict) or set(payload) != {
        "static_eligibility",
        "structural_novelty",
        "structural_rejection",
    }:
        raise StructuralScreenCacheError(
            "structural-screen annotation fields are incomplete"
        )
    static = payload["static_eligibility"]
    novelty = payload["structural_novelty"]
    if (
        not isinstance(static, dict)
        or static.get("checked") is not True
        or not isinstance(static.get("eligible"), bool)
        or not isinstance(novelty, dict)
        or not isinstance(novelty.get("checked"), bool)
        or not isinstance(novelty.get("novel"), bool)
    ):
        raise StructuralScreenCacheError(
            "structural-screen annotation has invalid gate markers"
        )
    checks = static.get("checks")
    failures = static.get("failures")
    if (
        not isinstance(checks, dict)
        or not checks
        or any(not isinstance(value, bool) for value in checks.values())
        or not isinstance(failures, list)
        or any(not isinstance(value, str) for value in failures)
        or static["eligible"] is not (
            all(checks.values()) and not failures
        )
    ):
        raise StructuralScreenCacheError(
            "structural-screen static evidence is internally inconsistent"
        )
    if static["eligible"]:
        basis_report = static.get("logical_basis_upper_bound")
        if basis_report is not None:
            _validate_logical_basis_upper_bound_report(basis_report)
        for name in ("n", "k"):
            value = static.get(name)
            if (
                isinstance(value, bool)
                or not isinstance(value, int)
                or value < 1
            ):
                raise StructuralScreenCacheError(
                    f"structural-screen annotation has invalid recomputed {name}"
                )
        digest = novelty.get("canonical_digest")
        if (
            novelty.get("checked") is not True
            or not isinstance(digest, str)
            or len(digest) != 64
            or any(character not in "0123456789abcdef" for character in digest)
        ):
            raise StructuralScreenCacheError(
                "eligible structural-screen annotation lacks canonical evidence"
            )
        if novelty["novel"]:
            if (
                payload["structural_rejection"] is not None
                or novelty.get("relation") is not None
                or novelty.get("matched_reference") is not None
                or novelty.get("reference_digest") is not None
                or novelty.get("explicit_isomorphism") is not None
            ):
                raise StructuralScreenCacheError(
                    "novel structural-screen annotation has rejection evidence"
                )
        else:
            replay = novelty.get("explicit_isomorphism")
            reference_digest = novelty.get("reference_digest")
            if (
                payload["structural_rejection"] != "known_reference"
                or novelty.get("relation")
                != "css_tanner_permutation_equivalent"
                or not isinstance(novelty.get("matched_reference"), str)
                or not novelty["matched_reference"]
                or not isinstance(reference_digest, str)
                or len(reference_digest) != 64
                or not isinstance(replay, dict)
                or replay.get("verified") is not True
            ):
                raise StructuralScreenCacheError(
                    "known-reference rejection lacks explicit replay"
                )
    elif (
        novelty.get("checked") is not False
        or novelty.get("relation") != "static_ineligible"
        or novelty.get("canonical_digest") is not None
        or novelty.get("matched_reference") is not None
        or novelty.get("reference_digest") is not None
        or novelty.get("explicit_isomorphism") is not None
        or payload["structural_rejection"] != "static_ineligible"
    ):
        raise StructuralScreenCacheError(
            "static rejection has inconsistent structural evidence"
        )


def _cache_entry_seal(entry: dict[str, Any]) -> str:
    unsigned = dict(entry)
    unsigned.pop("seal_sha256", None)
    return _sha256_json(unsigned)


def _cache_path(cache_dir: Path, input_sha256: str) -> Path:
    return cache_dir / input_sha256[:2] / f"{input_sha256}.json"


def _validate_cache_root(cache_dir: Path) -> None:
    if cache_dir.is_symlink():
        raise StructuralScreenCacheError(
            f"structural-screen cache may not be a symlink: {cache_dir}"
        )
    cache_dir.mkdir(parents=True, exist_ok=True)
    if not cache_dir.is_dir():
        raise StructuralScreenCacheError(
            f"structural-screen cache is not a directory: {cache_dir}"
        )


def _read_cache_entry(
    path: Path,
    *,
    screen_input: dict[str, Any],
    input_sha256: str,
    runtime_sha256: str,
) -> dict[str, Any] | None:
    if path.parent.is_symlink():
        raise StructuralScreenCacheError(
            f"structural-screen cache shard may not be a symlink: {path.parent}"
        )
    if path.parent.exists() and not path.parent.is_dir():
        raise StructuralScreenCacheError(
            f"structural-screen cache shard is not a directory: {path.parent}"
        )
    if path.is_symlink():
        raise StructuralScreenCacheError(
            f"structural-screen cache entry may not be a symlink: {path}"
        )
    if not path.exists():
        return None
    if not path.is_file():
        raise StructuralScreenCacheError(
            f"structural-screen cache entry is not a file: {path}"
        )
    try:
        entry = json.loads(path.read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StructuralScreenCacheError(
            f"cannot decode structural-screen cache entry: {path}"
        ) from exc
    expected_fields = {
        "schema_version",
        "input",
        "input_sha256",
        "runtime_sha256",
        "status",
        "annotation",
        "failure",
        "attempt_count",
        "seal_sha256",
    }
    if not isinstance(entry, dict) or set(entry) != expected_fields:
        raise StructuralScreenCacheError(
            f"structural-screen cache schema is invalid: {path}"
        )
    if (
        entry["schema_version"] != STRUCTURAL_SCREEN_CACHE_SCHEMA_VERSION
        or entry["input"] != screen_input
        or entry["input_sha256"] != input_sha256
        or entry["seal_sha256"] != _cache_entry_seal(entry)
    ):
        raise StructuralScreenCacheError(
            f"structural-screen cache integrity check failed: {path}"
        )
    attempts = entry["attempt_count"]
    if (
        isinstance(attempts, bool)
        or not isinstance(attempts, int)
        or attempts < 1
    ):
        raise StructuralScreenCacheError(
            f"structural-screen cache attempt count is invalid: {path}"
        )
    status = entry["status"]
    if status not in {"complete", "unresolved"}:
        raise StructuralScreenCacheError(
            f"structural-screen cache status is invalid: {path}"
        )
    if status == "complete":
        if entry["failure"] is not None:
            raise StructuralScreenCacheError(
                f"complete structural-screen cache has a failure: {path}"
            )
        _validate_annotation_payload(entry["annotation"])
    elif (
        entry["annotation"] is not None
        or not isinstance(entry["failure"], dict)
        or entry["failure"].get("retryable") is not True
    ):
        raise StructuralScreenCacheError(
            f"unresolved structural-screen cache is not retryable: {path}"
        )

    # A valid entry from an older source/runtime is stale evidence, not
    # corruption. Leave it in place until the current runtime atomically
    # replaces it after recomputation.
    if entry["runtime_sha256"] != runtime_sha256:
        return None
    return entry


def _write_cache_entry(
    path: Path,
    *,
    screen_input: dict[str, Any],
    input_sha256: str,
    runtime_sha256: str,
    status: str,
    annotation: dict[str, Any] | None,
    failure: dict[str, Any] | None,
    attempt_count: int,
) -> None:
    if path.is_symlink():
        raise StructuralScreenCacheError(
            f"structural-screen cache entry may not be a symlink: {path}"
        )
    if path.parent.is_symlink():
        raise StructuralScreenCacheError(
            f"structural-screen cache shard may not be a symlink: {path.parent}"
        )
    if path.parent.exists() and not path.parent.is_dir():
        raise StructuralScreenCacheError(
            f"structural-screen cache shard is not a directory: {path.parent}"
        )
    entry = {
        "schema_version": STRUCTURAL_SCREEN_CACHE_SCHEMA_VERSION,
        "input": screen_input,
        "input_sha256": input_sha256,
        "runtime_sha256": runtime_sha256,
        "status": status,
        "annotation": annotation,
        "failure": failure,
        "attempt_count": attempt_count,
        "seal_sha256": "",
    }
    entry["seal_sha256"] = _cache_entry_seal(entry)
    _atomic_write_json(path, entry)


def _normalized_pair_input(
    candidate: dict[str, Any],
    representative: dict[str, Any],
) -> dict[str, Any]:
    candidate_payload = {
        "static_eligibility": candidate.get("static_eligibility"),
        "structural_novelty": candidate.get("structural_novelty"),
        "structural_rejection": candidate.get("structural_rejection"),
    }
    representative_payload = {
        "static_eligibility": representative.get("static_eligibility"),
        "structural_novelty": representative.get("structural_novelty"),
        "structural_rejection": representative.get("structural_rejection"),
    }
    _validate_annotation_payload(candidate_payload)
    _validate_annotation_payload(representative_payload)
    candidate_static = candidate_payload["static_eligibility"]
    representative_static = representative_payload["static_eligibility"]
    candidate_novelty = candidate_payload["structural_novelty"]
    representative_novelty = representative_payload["structural_novelty"]
    candidate_key = (
        int(candidate_static["n"]),
        int(candidate_static["k"]),
        candidate_novelty["canonical_digest"],
    )
    representative_key = (
        int(representative_static["n"]),
        int(representative_static["k"]),
        representative_novelty["canonical_digest"],
    )
    if (
        not candidate_static["eligible"]
        or not representative_static["eligible"]
        or not candidate_novelty["novel"]
        or not representative_novelty["novel"]
        or candidate_key != representative_key
    ):
        raise StructuralScreenCacheError(
            "within-pool replay pair does not share one novel canonical key"
        )
    def check_counts(
        static: Mapping[str, Any], row: Mapping[str, Any],
    ) -> tuple[int, int]:
        rx, rz = static.get("x_checks"), static.get("z_checks")
        if (
            isinstance(rx, int) and not isinstance(rx, bool) and rx >= 0
            and isinstance(rz, int) and not isinstance(rz, bool) and rz >= 0
        ):
            return int(rx), int(rz)
        normalized = _normalized_screen_input(dict(row))
        if "ell" in normalized and "m" in normalized:
            block = int(normalized["ell"]) * int(normalized["m"])
            return block, block
        hx, hz = _matrices(_build_css_result(row))
        return int(hx.shape[0]), int(hz.shape[0])

    candidate_counts = check_counts(candidate_static, candidate)
    representative_counts = check_counts(
        representative_static, representative,
    )
    if candidate_counts != representative_counts:
        raise StructuralScreenCacheError(
            "within-pool replay pair has different check dimensions"
        )
    return {
        "candidate": _normalized_screen_input(candidate),
        "representative": _normalized_screen_input(representative),
        "recomputed_n": candidate_key[0],
        "recomputed_k": candidate_key[1],
        "recomputed_x_checks": candidate_counts[0],
        "recomputed_z_checks": candidate_counts[1],
        "canonical_digest": candidate_key[2],
    }


def structural_pair_input_sha256(
    candidate: dict[str, Any],
    representative: dict[str, Any],
) -> str:
    """Bind one ordered candidate/representative structural replay."""

    return _sha256_json(
        _normalized_pair_input(candidate, representative)
    )


def _pair_cache_path(cache_dir: Path, input_sha256: str) -> Path:
    return (
        cache_dir
        / "within-pool-isomorphism-v1"
        / input_sha256[:2]
        / f"{input_sha256}.json"
    )


def _read_pair_cache_entry(
    path: Path,
    *,
    pair_input: dict[str, Any],
    input_sha256: str,
    runtime_sha256: str,
) -> dict[str, Any] | None:
    if path.parent.is_symlink():
        raise StructuralScreenCacheError(
            f"within-pool cache shard may not be a symlink: {path.parent}"
        )
    if path.parent.exists() and not path.parent.is_dir():
        raise StructuralScreenCacheError(
            f"within-pool cache shard is not a directory: {path.parent}"
        )
    if path.is_symlink():
        raise StructuralScreenCacheError(
            f"within-pool cache entry may not be a symlink: {path}"
        )
    if not path.exists():
        return None
    if not path.is_file():
        raise StructuralScreenCacheError(
            f"within-pool cache entry is not a file: {path}"
        )
    try:
        entry = json.loads(path.read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StructuralScreenCacheError(
            f"cannot decode within-pool cache entry: {path}"
        ) from exc
    expected_fields = {
        "schema_version",
        "input",
        "input_sha256",
        "runtime_sha256",
        "status",
        "replay",
        "failure",
        "attempt_count",
        "seal_sha256",
    }
    if not isinstance(entry, dict) or set(entry) != expected_fields:
        raise StructuralScreenCacheError(
            f"within-pool cache schema is invalid: {path}"
        )
    if (
        entry["schema_version"] != STRUCTURAL_PAIR_CACHE_SCHEMA_VERSION
        or entry["input"] != pair_input
        or entry["input_sha256"] != input_sha256
        or entry["seal_sha256"] != _cache_entry_seal(entry)
    ):
        raise StructuralScreenCacheError(
            f"within-pool cache integrity check failed: {path}"
        )
    attempts = entry["attempt_count"]
    if (
        isinstance(attempts, bool)
        or not isinstance(attempts, int)
        or attempts < 1
    ):
        raise StructuralScreenCacheError(
            f"within-pool cache attempt count is invalid: {path}"
        )
    status = entry["status"]
    if status not in {"complete", "unresolved"}:
        raise StructuralScreenCacheError(
            f"within-pool cache status is invalid: {path}"
        )
    if status == "complete":
        if entry["failure"] is not None:
            raise StructuralScreenCacheError(
                f"complete within-pool cache has a failure: {path}"
            )
        _validate_pair_replay_payload(
            entry["replay"],
            pair_input=pair_input,
        )
    elif (
        entry["replay"] is not None
        or not isinstance(entry["failure"], dict)
        or entry["failure"].get("retryable") is not True
    ):
        raise StructuralScreenCacheError(
            f"unresolved within-pool cache is not retryable: {path}"
        )
    if entry["runtime_sha256"] != runtime_sha256:
        return None
    return entry


def _write_pair_cache_entry(
    path: Path,
    *,
    pair_input: dict[str, Any],
    input_sha256: str,
    runtime_sha256: str,
    status: str,
    replay: dict[str, Any] | None,
    failure: dict[str, Any] | None,
    attempt_count: int,
) -> None:
    if path.is_symlink():
        raise StructuralScreenCacheError(
            f"within-pool cache entry may not be a symlink: {path}"
        )
    if path.parent.is_symlink():
        raise StructuralScreenCacheError(
            f"within-pool cache shard may not be a symlink: {path.parent}"
        )
    if path.parent.exists() and not path.parent.is_dir():
        raise StructuralScreenCacheError(
            f"within-pool cache shard is not a directory: {path.parent}"
        )
    entry = {
        "schema_version": STRUCTURAL_PAIR_CACHE_SCHEMA_VERSION,
        "input": pair_input,
        "input_sha256": input_sha256,
        "runtime_sha256": runtime_sha256,
        "status": status,
        "replay": replay,
        "failure": failure,
        "attempt_count": attempt_count,
        "seal_sha256": "",
    }
    entry["seal_sha256"] = _cache_entry_seal(entry)
    _atomic_write_json(path, entry)


def _structural_annotation_worker(connection) -> None:
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    while True:
        try:
            message = connection.recv()
        except EOFError:
            return
        if message is None:
            return
        task_index, result = message
        connection.send(("started", task_index, None))
        try:
            _require_structural_screen_native_thread_environment()
            annotation = _annotation_payload(result)
        except BaseException as exc:
            connection.send((
                "error",
                task_index,
                {
                    "kind": "worker_error",
                    "exception_type": type(exc).__name__,
                    "message": str(exc)[:1000],
                    "retryable": True,
                },
            ))
        else:
            connection.send(("result", task_index, annotation))


def _validate_pair_replay_payload(
    payload: Any,
    *,
    pair_input: dict[str, Any] | None = None,
) -> None:
    expected_fields = {
        "verified",
        "hx_preserved",
        "hz_preserved",
        "qubit_permutation",
        "x_check_permutation",
        "z_check_permutation",
    }
    if (
        not isinstance(payload, dict)
        or set(payload) != expected_fields
        or payload["verified"] is not True
        or payload["hx_preserved"] is not True
        or payload["hz_preserved"] is not True
    ):
        raise StructuralScreenCacheError(
            "within-pool isomorphism replay is incomplete"
        )
    permutations = (
        payload["qubit_permutation"],
        payload["x_check_permutation"],
        payload["z_check_permutation"],
    )
    if any(
        not isinstance(permutation, list)
        or any(
            isinstance(value, bool) or not isinstance(value, int)
            for value in permutation
        )
        for permutation in permutations
    ):
        raise StructuralScreenCacheError(
            "within-pool isomorphism replay has invalid permutations"
        )
    if pair_input is None:
        return
    n = int(pair_input["recomputed_n"])
    rx = int(pair_input["recomputed_x_checks"])
    rz = int(pair_input["recomputed_z_checks"])
    if n <= 0 or rx < 0 or rz < 0:
        raise StructuralScreenCacheError(
            "within-pool isomorphism pair has inconsistent dimensions"
        )
    expected_permutations = (
        list(range(n)),
        list(range(rx)),
        list(range(rz)),
    )
    if any(
        sorted(observed) != expected
        for observed, expected in zip(
            permutations,
            expected_permutations,
            strict=True,
        )
    ):
        raise StructuralScreenCacheError(
            "within-pool isomorphism replay violates color partitions"
        )


def _pair_replay_payload(task: dict[str, Any]) -> dict[str, Any]:
    candidate = task["candidate"]
    representative = task["representative"]
    candidate_code = _build_css_result(candidate)
    representative_code = _build_css_result(representative)
    mapping = extract_full_vertex_isomorphism(
        candidate_code,
        representative_code,
    )
    if mapping is None:
        raise RuntimeError("within-run canonical match lacked isomorphism")
    replay = replay_css_isomorphism(
        candidate_code,
        representative_code,
        mapping,
    )
    if not replay["verified"]:
        raise RuntimeError("within-run isomorphism failed matrix replay")
    _validate_pair_replay_payload(replay)
    return replay


def _structural_pair_worker(connection) -> None:
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    while True:
        try:
            message = connection.recv()
        except EOFError:
            return
        if message is None:
            return
        task_index, task = message
        connection.send(("started", task_index, None))
        try:
            _require_structural_screen_native_thread_environment()
            replay = _pair_replay_payload(task)
        except BaseException as exc:
            connection.send((
                "error",
                task_index,
                {
                    "kind": "worker_error",
                    "exception_type": type(exc).__name__,
                    "message": str(exc)[:1000],
                    "retryable": True,
                },
            ))
        else:
            connection.send(("result", task_index, replay))


def _stop_annotation_worker(process, connection) -> None:
    try:
        if process.is_alive():
            process.terminate()
            process.join(timeout=2.0)
        if process.is_alive():
            process.kill()
            process.join(timeout=2.0)
    finally:
        connection.close()


def _stop_annotation_workers(workers: list[dict[str, Any]]) -> None:
    """Stop an idle worker cohort without paying one timeout per process."""

    active = [worker for worker in workers if not worker.get("closed")]
    if not active:
        return
    try:
        # Signal the full cohort first.  Joining each process immediately after
        # terminating it serialized native-runtime teardown in production.
        for worker in active:
            process = worker["process"]
            if process.is_alive():
                process.terminate()

        terminate_deadline = time.monotonic() + 2.0
        for worker in active:
            process = worker["process"]
            if process.is_alive():
                process.join(timeout=max(
                    0.0,
                    terminate_deadline - time.monotonic(),
                ))

        survivors = [
            worker["process"]
            for worker in active
            if worker["process"].is_alive()
        ]
        for process in survivors:
            process.kill()
        kill_deadline = time.monotonic() + 2.0
        for process in survivors:
            if process.is_alive():
                process.join(timeout=max(
                    0.0,
                    kill_deadline - time.monotonic(),
                ))
    finally:
        for worker in active:
            worker["connection"].close()


def _run_hard_wall_workers(
    tasks: list[tuple[int, Any]],
    *,
    max_workers: int,
    hard_timeout: float,
    worker_target: Callable[[Any], None],
    validate_result: Callable[[Any], None],
    protocol_name: str,
    on_completed: Callable[[int, Any], None] | None = None,
    on_unresolved: Callable[[int, dict[str, Any]], None] | None = None,
) -> tuple[dict[int, Any], dict[int, dict[str, Any]]]:
    """Run ordered tasks in replaceable processes with a per-task wall clock."""

    if (
        isinstance(max_workers, bool)
        or not isinstance(max_workers, int)
        or max_workers < 1
    ):
        raise ValueError("max_workers must be a positive integer")
    if (
        isinstance(hard_timeout, bool)
        or not isinstance(hard_timeout, (int, float))
        or not math.isfinite(float(hard_timeout))
        or hard_timeout <= 0
    ):
        raise ValueError("hard_timeout must be a positive finite number")
    if not tasks:
        return {}, {}

    context = multiprocessing.get_context("spawn")
    pending = deque(tasks)
    completed: dict[int, Any] = {}
    unresolved: dict[int, dict[str, Any]] = {}
    workers: list[dict[str, Any]] = []

    def spawn_worker() -> dict[str, Any]:
        parent_connection, child_connection = context.Pipe()
        process = context.Process(
            target=worker_target,
            args=(child_connection,),
            daemon=False,
        )
        with _structural_screen_spawn_environment():
            process.start()
        child_connection.close()
        return {
            "process": process,
            "connection": parent_connection,
            "task": None,
            "deadline": None,
        }

    def assign(worker: dict[str, Any]) -> None:
        if worker["task"] is not None or not pending:
            return
        task = pending.popleft()
        worker["connection"].send(task)
        worker["task"] = task
        # Include process startup/import time in the hard wall clock.
        worker["deadline"] = time.monotonic() + float(hard_timeout)

    try:
        for _ in range(min(max_workers, len(tasks))):
            worker = spawn_worker()
            workers.append(worker)
            assign(worker)

        while pending or any(worker["task"] is not None for worker in workers):
            made_progress = False
            now = time.monotonic()
            for index, worker in enumerate(list(workers)):
                process = worker["process"]
                connection = worker["connection"]
                task = worker["task"]
                while connection.poll():
                    made_progress = True
                    try:
                        kind, task_index, payload = connection.recv()
                    except EOFError:
                        break
                    if task is None or task_index != task[0]:
                        raise StructuralScreenCacheError(
                            f"{protocol_name} worker protocol mismatch"
                        )
                    if kind == "started":
                        continue
                    if kind == "result":
                        validate_result(payload)
                        completed[task_index] = payload
                        if on_completed is not None:
                            on_completed(task_index, payload)
                    elif kind == "error":
                        if (
                            not isinstance(payload, dict)
                            or payload.get("retryable") is not True
                        ):
                            raise StructuralScreenCacheError(
                                f"{protocol_name} worker error is invalid"
                            )
                        unresolved[task_index] = payload
                        if on_unresolved is not None:
                            on_unresolved(task_index, payload)
                    else:
                        raise StructuralScreenCacheError(
                            f"{protocol_name} worker returned an unknown message"
                        )
                    worker["task"] = None
                    worker["deadline"] = None
                    task = None
                    if kind == "error":
                        _stop_annotation_worker(process, connection)
                        replacement = spawn_worker() if pending else None
                        workers[index] = replacement or {
                            "process": process,
                            "connection": connection,
                            "task": None,
                            "deadline": None,
                            "closed": True,
                        }
                        worker = workers[index]
                    break

                if worker.get("closed"):
                    continue
                task = worker["task"]
                if task is not None and now >= worker["deadline"]:
                    made_progress = True
                    unresolved[task[0]] = {
                        "kind": "hard_timeout",
                        "hard_timeout_seconds": float(hard_timeout),
                        "retryable": True,
                    }
                    if on_unresolved is not None:
                        on_unresolved(task[0], unresolved[task[0]])
                    process.terminate()
                    process.join(timeout=2.0)
                    if process.is_alive():
                        process.kill()
                        process.join(timeout=2.0)
                    connection.close()
                    replacement = spawn_worker() if pending else None
                    workers[index] = replacement or {
                        "process": process,
                        "connection": connection,
                        "task": None,
                        "deadline": None,
                        "closed": True,
                    }
                    worker = workers[index]

                if not worker.get("closed") and not worker["process"].is_alive():
                    task = worker["task"]
                    if task is not None:
                        unresolved[task[0]] = {
                            "kind": "worker_exit",
                            "exit_code": worker["process"].exitcode,
                            "retryable": True,
                        }
                        if on_unresolved is not None:
                            on_unresolved(task[0], unresolved[task[0]])
                    worker["connection"].close()
                    replacement = spawn_worker() if pending else None
                    workers[index] = replacement or {
                        **worker,
                        "task": None,
                        "deadline": None,
                        "closed": True,
                    }
                    worker = workers[index]
                    made_progress = True

                if not worker.get("closed"):
                    assign(worker)
            if not made_progress:
                time.sleep(0.02)
    finally:
        _stop_annotation_workers(workers)
    return completed, unresolved


def _run_annotation_workers(
    tasks: list[tuple[int, dict[str, Any]]],
    *,
    max_workers: int,
    hard_timeout: float,
    on_completed: Callable[[int, dict[str, Any]], None] | None = None,
    on_unresolved: Callable[[int, dict[str, Any]], None] | None = None,
) -> tuple[dict[int, dict[str, Any]], dict[int, dict[str, Any]]]:
    """Run annotations in replaceable processes with a per-task wall clock."""

    return _run_hard_wall_workers(
        tasks,
        max_workers=max_workers,
        hard_timeout=hard_timeout,
        worker_target=_structural_annotation_worker,
        validate_result=_validate_annotation_payload,
        protocol_name="structural-screen",
        on_completed=on_completed,
        on_unresolved=on_unresolved,
    )


def _run_isomorphism_workers(
    tasks: list[tuple[int, dict[str, Any]]],
    *,
    max_workers: int,
    hard_timeout: float,
    on_completed: Callable[[int, dict[str, Any]], None] | None = None,
    on_unresolved: Callable[[int, dict[str, Any]], None] | None = None,
) -> tuple[dict[int, dict[str, Any]], dict[int, dict[str, Any]]]:
    """Replay candidate/representative pairs behind the same hard wall."""

    return _run_hard_wall_workers(
        tasks,
        max_workers=max_workers,
        hard_timeout=hard_timeout,
        worker_target=_structural_pair_worker,
        validate_result=_validate_pair_replay_payload,
        protocol_name="within-pool isomorphism",
        on_completed=on_completed,
        on_unresolved=on_unresolved,
    )


def _matrices(code):
    hx = np.asarray(
        code.matrix_x.toarray() if hasattr(code.matrix_x, "toarray")
        else code.matrix_x, dtype=np.uint8,
    ) & 1
    hz = np.asarray(
        code.matrix_z.toarray() if hasattr(code.matrix_z, "toarray")
        else code.matrix_z, dtype=np.uint8,
    ) & 1
    return hx, hz


def _has_compact_construction(result: Mapping[str, Any]) -> bool:
    return isinstance(result.get("construction"), Mapping)


def _build_css_result(result: Mapping[str, Any]):
    """Rebuild either a compact construction or a legacy BB record."""

    if _has_compact_construction(result):
        from evaluation.construction import build_css_code_from_claim

        return build_css_code_from_claim(dict(result))
    ell, m = int(result["ell"]), int(result["m"])
    return build_bb_code(
        ell,
        m,
        result["A_terms"],
        result["B_terms"],
        geometry=candidate_geometry(result),
    )


def _code_parameters(code) -> tuple[int, int]:
    try:
        n = int(code.num_qudits)
        k = int(code.dimension)
    except (AttributeError, TypeError, ValueError, OverflowError) as exc:
        raise ValueError("rebuilt CSS code has invalid n/k parameters") from exc
    if n <= 0:
        raise ValueError("rebuilt CSS code has non-positive block length")
    return n, k


def _component_sizes(checks: np.ndarray) -> list[int]:
    """Return Tanner-component sizes using the final gate's graph definition."""
    matrix = np.asarray(checks, dtype=np.uint8) & 1
    num_checks, num_qubits = matrix.shape
    adjacency = [[] for _ in range(num_checks + num_qubits)]
    for check_index, qubit_index in np.argwhere(matrix):
        left = int(check_index)
        right = num_checks + int(qubit_index)
        adjacency[left].append(right)
        adjacency[right].append(left)

    unseen = set(range(len(adjacency)))
    sizes = []
    while unseen:
        start = unseen.pop()
        size = 0
        stack = [start]
        while stack:
            node = stack.pop()
            size += 1
            for neighbor in adjacency[node]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
        sizes.append(size)
    return sorted(sizes, reverse=True)


def _check_css_static_eligibility_with_code(
    ell, m, a_terms, b_terms, *, geometry=None, reported_n=None, reported_k=None,
) -> tuple[dict[str, Any], Any | None]:
    """Run cheap, fail-closed challenge gates before BLISS or distance MILP.

    The code is rebuilt, then commutation, check weight, qubit degree, positive
    dimension, and connectedness are recomputed from H_X/H_Z. Optional reported
    n/k values are cross-checked but never trusted as inputs to those checks.
    """
    try:
        ell, m = int(ell), int(m)
        a_terms = [tuple(map(int, term)) for term in a_terms]
        b_terms = [tuple(map(int, term)) for term in b_terms]
        validate_terms(ell, m, a_terms, "A")
        validate_terms(ell, m, b_terms, "B")
        geometry = normalize_geometry(ell, m, geometry)
        code = build_bb_code(
            ell, m, a_terms, b_terms, geometry=geometry,
        )
        hx, hz = _matrices(code)
    except (TypeError, ValueError) as exc:
        return {
            "checked": True,
            "eligible": False,
            "checks": {"candidate_rebuild": False},
            "failures": [f"candidate_rebuild: {exc}"],
        }, None

    stacked = np.vstack((hx, hz))
    component_sizes = _component_sizes(stacked)
    max_row_weight = int(stacked.sum(axis=1).max(initial=0))
    max_qubit_degree = int(stacked.sum(axis=0).max(initial=0))
    n, k = get_code_params_fast(code)
    checks = {
        "candidate_rebuild": True,
        "positive_dimension": int(k) > 0,
        "css_commutation": int(np.count_nonzero((hx @ hz.T) & 1)) == 0,
        "weight_and_degree_at_most_6": (
            max_row_weight <= 6 and max_qubit_degree <= 6
        ),
        "connected_tanner_graph": len(component_sizes) == 1,
    }
    if reported_n is not None:
        checks["reported_n_matches"] = int(reported_n) == int(n)
    if reported_k is not None:
        checks["reported_k_matches"] = int(reported_k) == int(k)
    failures = [name for name, passed in checks.items() if not passed]
    return {
        "checked": True,
        "eligible": not failures,
        "checks": checks,
        "failures": failures,
        "n": int(n),
        "k": int(k),
        "x_checks": int(hx.shape[0]),
        "z_checks": int(hz.shape[0]),
        "max_row_weight": max_row_weight,
        "max_qubit_degree": max_qubit_degree,
        "tanner_components": len(component_sizes),
        "tanner_component_sizes": component_sizes,
    }, code


def check_css_static_eligibility(
    ell, m, a_terms, b_terms, *, geometry=None, reported_n=None, reported_k=None,
) -> dict:
    """Run the public static challenge gate without exposing rebuilt state."""

    report, _code = _check_css_static_eligibility_with_code(
        ell,
        m,
        a_terms,
        b_terms,
        geometry=geometry,
        reported_n=reported_n,
        reported_k=reported_k,
    )
    return report


def _check_css_result_static_eligibility_with_code(
    result: Mapping[str, Any],
) -> tuple[dict[str, Any], Any | None]:
    """Run the static gate and retain its already-verified rebuilt code."""

    if not _has_compact_construction(result):
        return _check_css_static_eligibility_with_code(
            int(result["ell"]),
            int(result["m"]),
            result["A_terms"],
            result["B_terms"],
            geometry=candidate_geometry(result),
            reported_n=result.get("n"),
            reported_k=result.get("k"),
        )
    try:
        code = _build_css_result(result)
        hx, hz = _matrices(code)
        n, k = _code_parameters(code)
    except (ImportError, KeyError, TypeError, ValueError, OverflowError) as exc:
        return {
            "checked": True,
            "eligible": False,
            "checks": {"candidate_rebuild": False},
            "failures": [f"candidate_rebuild: {exc}"],
        }, None
    stacked = np.vstack((hx, hz))
    component_sizes = _component_sizes(stacked)
    max_row_weight = int(stacked.sum(axis=1).max(initial=0))
    max_qubit_degree = int(stacked.sum(axis=0).max(initial=0))
    checks = {
        "candidate_rebuild": True,
        "positive_dimension": k > 0,
        "css_commutation": int(np.count_nonzero((hx @ hz.T) & 1)) == 0,
        "weight_and_degree_at_most_6": (
            max_row_weight <= 6 and max_qubit_degree <= 6
        ),
        "connected_tanner_graph": len(component_sizes) == 1,
    }
    if result.get("n") is not None:
        checks["reported_n_matches"] = (
            type(result["n"]) is int and int(result["n"]) == n
        )
    if result.get("k") is not None:
        checks["reported_k_matches"] = (
            type(result["k"]) is int and int(result["k"]) == k
        )
    failures = [name for name, passed in checks.items() if not passed]
    return {
        "checked": True,
        "eligible": not failures,
        "checks": checks,
        "failures": failures,
        "n": n,
        "k": k,
        "x_checks": int(hx.shape[0]),
        "z_checks": int(hz.shape[0]),
        "max_row_weight": max_row_weight,
        "max_qubit_degree": max_qubit_degree,
        "tanner_components": len(component_sizes),
        "tanner_component_sizes": component_sizes,
    }, code


def check_css_result_static_eligibility(result: Mapping[str, Any]) -> dict:
    """Run the static challenge gate on any supported CSS construction."""

    report, _code = _check_css_result_static_eligibility_with_code(result)
    return report


def _canonical_digest_from_hash(canonical: tuple[tuple[int, int], ...]) -> str:
    """Digest one already-computed BLISS canonical edge representation."""

    digest = hashlib.sha256()
    for left, right in canonical:
        digest.update(int(left).to_bytes(4, "little"))
        digest.update(int(right).to_bytes(4, "little"))
    return digest.hexdigest()


def canonical_digest(code) -> str:
    """Compact, stable digest of the BLISS canonical edge representation."""

    return _canonical_digest_from_hash(canonical_hash(code))


def replay_css_isomorphism(code_a, code_b, mapping) -> dict:
    """Replay a BLISS mapping directly on H_X and H_Z."""
    hx_a, hz_a = _matrices(code_a)
    hx_b, hz_b = _matrices(code_b)
    n = hx_a.shape[1]
    rx, rz = hx_a.shape[0], hz_a.shape[0]
    if (
        hx_b.shape != hx_a.shape
        or hz_b.shape != hz_a.shape
        or len(mapping) != n + rx + rz
    ):
        return {"verified": False, "reason": "matrix or mapping shape mismatch"}

    qubits = np.asarray(mapping[:n], dtype=int)
    x_rows = np.asarray(mapping[n:n + rx], dtype=int) - n
    z_rows = np.asarray(mapping[n + rx:], dtype=int) - n - rx
    valid = (
        sorted(qubits.tolist()) == list(range(n))
        and sorted(x_rows.tolist()) == list(range(rx))
        and sorted(z_rows.tolist()) == list(range(rz))
    )
    if not valid:
        return {"verified": False, "reason": "mapping violates color partitions"}

    hx_ok = np.array_equal(hx_a, hx_b[np.ix_(x_rows, qubits)])
    hz_ok = np.array_equal(hz_a, hz_b[np.ix_(z_rows, qubits)])
    return {
        "verified": bool(hx_ok and hz_ok),
        "hx_preserved": bool(hx_ok),
        "hz_preserved": bool(hz_ok),
        "qubit_permutation": qubits.tolist(),
        "x_check_permutation": x_rows.tolist(),
        "z_check_permutation": z_rows.tolist(),
    }


@lru_cache(maxsize=1)
def known_reference_registry():
    """Build canonical forms for the literature registry once per process."""
    registry = []
    for name, ell, m, a_terms, b_terms in KNOWN_CSS_REFERENCES:
        code = build_bb_code(ell, m, a_terms, b_terms)
        n, k = get_code_params_fast(code)
        canonical = canonical_hash(code)
        registry.append({
            "name": name,
            "ell": ell,
            "m": m,
            "A_terms": a_terms,
            "B_terms": b_terms,
            "n": int(n),
            "k": int(k),
            "canonical_hash": canonical,
            "canonical_digest": _canonical_digest_from_hash(canonical),
            "code": code,
        })
    return tuple(registry)


def check_css_structural_novelty(
    ell, m, a_terms, b_terms, *, geometry=None,
) -> dict:
    """Classify a CSS BB candidate against known literature structures."""
    candidate = build_bb_code(
        ell,
        m,
        a_terms,
        b_terms,
        geometry=normalize_geometry(ell, m, geometry),
    )
    return check_css_code_structural_novelty(candidate)


def check_css_code_structural_novelty(candidate) -> dict:
    """Classify an arbitrary rebuilt CSS code by Tanner equivalence."""

    n, k = _code_parameters(candidate)
    return _check_css_code_structural_novelty_with_parameters(
        candidate,
        n=n,
        k=k,
    )


def _check_css_code_structural_novelty_with_parameters(
    candidate,
    *,
    n: int,
    k: int,
) -> dict:
    """Classify a code whose dimensions were verified by the static gate."""

    candidate_hash = canonical_hash(candidate)
    candidate_digest = _canonical_digest_from_hash(candidate_hash)

    for reference in known_reference_registry():
        if reference["n"] != n or reference["k"] != k:
            continue
        if reference["canonical_hash"] != candidate_hash:
            continue
        mapping = extract_full_vertex_isomorphism(candidate, reference["code"])
        if mapping is None:
            raise RuntimeError("canonical match did not yield an isomorphism")
        replay = replay_css_isomorphism(candidate, reference["code"], mapping)
        if not replay["verified"]:
            raise RuntimeError("BLISS isomorphism failed explicit matrix replay")
        return {
            "checked": True,
            "novel": False,
            "relation": "css_tanner_permutation_equivalent",
            "canonical_digest": candidate_digest,
            "matched_reference": reference["name"],
            "reference_digest": reference["canonical_digest"],
            "explicit_isomorphism": replay,
        }

    return {
        "checked": True,
        "novel": True,
        "relation": None,
        "canonical_digest": candidate_digest,
        "matched_reference": None,
        "reference_digest": None,
        "explicit_isomorphism": None,
    }


def annotate_css_result(result: dict) -> dict:
    """Return a result copy carrying static and structural eligibility audits."""
    annotated = dict(result)
    annotated.pop(STRUCTURAL_PAIR_REPLAY_FIELD, None)
    static, code = _check_css_result_static_eligibility_with_code(result)
    annotated["static_eligibility"] = static
    if not static["eligible"]:
        annotated["structural_novelty"] = {
            "checked": False,
            "novel": False,
            "relation": "static_ineligible",
            "canonical_digest": None,
            "matched_reference": None,
            "reference_digest": None,
            "explicit_isomorphism": None,
        }
        annotated["structural_rejection"] = "static_ineligible"
        return annotated
    if code is None:  # Defensive: eligible reports must retain their rebuild.
        raise RuntimeError("eligible structural screen lost rebuilt CSS code")
    annotated["structural_novelty"] = (
        _check_css_code_structural_novelty_with_parameters(
            code,
            n=int(static["n"]),
            k=int(static["k"]),
        )
    )
    if not annotated["structural_novelty"]["novel"]:
        annotated["structural_rejection"] = "known_reference"
    else:
        static["logical_basis_upper_bound"] = (
            _logical_basis_upper_bound_report(code)
        )
    return annotated


def _apply_annotation_payload(
    result: dict[str, Any],
    payload: dict[str, Any],
) -> dict[str, Any]:
    _validate_annotation_payload(payload)
    annotated = dict(result)
    annotated.pop(STRUCTURAL_PAIR_REPLAY_FIELD, None)
    annotated["static_eligibility"] = copy.deepcopy(
        payload["static_eligibility"]
    )
    annotated["structural_novelty"] = copy.deepcopy(
        payload["structural_novelty"]
    )
    rejection = payload["structural_rejection"]
    if rejection is None:
        annotated.pop("structural_rejection", None)
    else:
        annotated["structural_rejection"] = rejection
    return annotated


def deduplicate_annotated_css_results(
    annotated_results: list[dict[str, Any]],
) -> tuple[list[dict], list[dict]]:
    """Deduplicate results carrying current, validated gate annotations.

    Canonical equality is only the index.  Every within-run match is replayed
    against H_X/H_Z before the later candidate is rejected.
    """
    kept: list[dict] = []
    rejected: list[dict] = []
    representatives: dict[tuple[int, int, str], dict[str, Any]] = {}
    for annotated in annotated_results:
        payload = {
            "static_eligibility": annotated.get("static_eligibility"),
            "structural_novelty": annotated.get("structural_novelty"),
            "structural_rejection": annotated.get("structural_rejection"),
        }
        _validate_annotation_payload(payload)
        static = annotated["static_eligibility"]
        if not static["eligible"]:
            rejected.append(annotated)
            continue
        audit = annotated["structural_novelty"]
        if not audit["novel"]:
            annotated["structural_rejection"] = "known_reference"
            rejected.append(annotated)
            continue

        # n/k came from the rebuilt matrices in static eligibility. Never use
        # the candidate's self-reported values to form the equivalence bucket.
        n, k = int(static["n"]), int(static["k"])
        key = (int(n), int(k), audit["canonical_digest"])
        previous = representatives.get(key)
        if previous is None:
            representatives[key] = annotated
            kept.append(annotated)
            continue

        candidate = _build_css_result(annotated)
        representative = previous
        representative_code = _build_css_result(representative)
        mapping = extract_full_vertex_isomorphism(candidate, representative_code)
        if mapping is None:
            raise RuntimeError("within-run canonical match lacked isomorphism")
        replay = replay_css_isomorphism(candidate, representative_code, mapping)
        if not replay["verified"]:
            raise RuntimeError("within-run isomorphism failed matrix replay")
        annotated["structural_novelty"] = {
            **audit,
            "novel": False,
            "relation": "within_run_css_tanner_permutation_equivalent",
            "matched_reference": representative.get("label") or (
                f"[[{representative.get('n')},{representative.get('k')},"
                f"{representative.get('d')}]]"
            ),
            "reference_digest": key[2],
            "explicit_isomorphism": replay,
        }
        annotated["structural_rejection"] = "within_run_duplicate"
        rejected.append(annotated)
    return kept, rejected


def deduplicate_css_results(results: list[dict]) -> tuple[list[dict], list[dict]]:
    """Reject known references and within-run permutation duplicates."""
    annotated = [annotate_css_result(result) for result in results]
    return deduplicate_annotated_css_results(annotated)


def _annotate_css_results_with_deferred_cache_indexed(
    results: list[dict[str, Any]],
    *,
    cache_dir: Path,
    max_workers: int,
    hard_timeout: float = STRUCTURAL_SCREEN_HARD_TIMEOUT_SECONDS,
) -> tuple[list[tuple[int, dict[str, Any]]], list[dict[str, Any]]]:
    """Annotate one ordered pool with durable, hard-walled evidence.

    Complete cache entries are evidence for only one normalized candidate
    input and one source/runtime fingerprint. Timeout and worker failures are
    persisted as retryable state and returned separately; they are never
    converted into structural rejection.

    This primitive deliberately does not perform within-pool isomorphism
    replay after the worker phase. The source indexes let the Stage 1 wrapper
    preserve exact pool order even when some annotation tasks are unresolved.
    """
    _validate_cache_root(cache_dir)
    runtime = structural_screen_runtime_fingerprint()
    runtime_sha256 = runtime["sha256"]
    annotations: dict[int, dict[str, Any]] = {}
    task_rows: list[tuple[int, dict[str, Any]]] = []
    task_metadata: dict[int, dict[str, Any]] = {}

    for index, result in enumerate(results):
        screen_input = _normalized_screen_input(result)
        input_sha256 = _sha256_json(screen_input)
        path = _cache_path(cache_dir, input_sha256)
        entry = _read_cache_entry(
            path,
            screen_input=screen_input,
            input_sha256=input_sha256,
            runtime_sha256=runtime_sha256,
        )
        if entry is not None and entry["status"] == "complete":
            annotations[index] = entry["annotation"]
            continue
        attempts = 0 if entry is None else int(entry["attempt_count"])
        task_metadata[index] = {
            "screen_input": screen_input,
            "input_sha256": input_sha256,
            "path": path,
            "attempt_count": attempts + 1,
        }
        task_rows.append((index, result))

    persisted_completed: set[int] = set()
    persisted_unresolved: set[int] = set()
    unresolved_evidence: list[dict[str, Any]] = []

    def persist_completed(
        index: int,
        annotation: dict[str, Any],
    ) -> None:
        metadata = task_metadata[index]
        _write_cache_entry(
            metadata["path"],
            screen_input=metadata["screen_input"],
            input_sha256=metadata["input_sha256"],
            runtime_sha256=runtime_sha256,
            status="complete",
            annotation=annotation,
            failure=None,
            attempt_count=metadata["attempt_count"],
        )
        annotations[index] = annotation
        persisted_completed.add(index)

    def persist_unresolved(
        index: int,
        failure: dict[str, Any],
    ) -> None:
        metadata = task_metadata[index]
        _write_cache_entry(
            metadata["path"],
            screen_input=metadata["screen_input"],
            input_sha256=metadata["input_sha256"],
            runtime_sha256=runtime_sha256,
            status="unresolved",
            annotation=None,
            failure=failure,
            attempt_count=metadata["attempt_count"],
        )
        unresolved_evidence.append({
            "candidate_index": index,
            "input_sha256": metadata["input_sha256"],
            "attempt_count": metadata["attempt_count"],
            "failure": copy.deepcopy(failure),
        })
        persisted_unresolved.add(index)

    if task_rows:
        completed, unresolved = _run_annotation_workers(
            task_rows,
            max_workers=max_workers,
            hard_timeout=hard_timeout,
            on_completed=persist_completed,
            on_unresolved=persist_unresolved,
        )
    else:
        completed, unresolved = {}, {}
    for index, annotation in completed.items():
        if index not in persisted_completed:
            persist_completed(index, annotation)
    for index, failure in unresolved.items():
        if index not in persisted_unresolved:
            persist_unresolved(index, failure)

    expected = set(task_metadata)
    observed = set(completed) | set(unresolved)
    if expected != observed or set(completed) & set(unresolved):
        raise StructuralScreenCacheError(
            "structural-screen worker results are incomplete or duplicated"
        )
    unresolved_evidence.sort(key=lambda item: item["candidate_index"])
    ordered = [
        (index, _apply_annotation_payload(result, annotations[index]))
        for index, result in enumerate(results)
        if index in annotations
    ]
    return ordered, unresolved_evidence


def annotate_css_results_with_deferred_cache(
    results: list[dict[str, Any]],
    *,
    cache_dir: Path,
    max_workers: int,
    hard_timeout: float = STRUCTURAL_SCREEN_HARD_TIMEOUT_SECONDS,
) -> tuple[list[dict], list[dict[str, Any]]]:
    """Annotate an ordered pool while retaining retryable failures."""

    indexed, unresolved = (
        _annotate_css_results_with_deferred_cache_indexed(
            results,
            cache_dir=cache_dir,
            max_workers=max_workers,
            hard_timeout=hard_timeout,
        )
    )
    return [row for _index, row in indexed], unresolved


def _deduplicate_indexed_with_deferred_cache(
    indexed_annotated: list[tuple[int, dict[str, Any]]],
    *,
    cache_dir: Path,
    max_workers: int,
    hard_timeout: float,
) -> tuple[list[dict], list[dict], list[dict[str, Any]]]:
    """Replay each duplicate pair in a cached, killable worker."""

    pair_cache_dir = cache_dir / "within-pool-isomorphism-v1"
    _validate_cache_root(pair_cache_dir)
    runtime_sha256 = structural_screen_runtime_fingerprint()["sha256"]
    representatives: dict[
        tuple[int, int, str],
        tuple[int, dict[str, Any]],
    ] = {}
    outcomes: dict[int, tuple[str, dict[str, Any]]] = {}
    pair_rows: dict[
        int,
        tuple[dict[str, Any], dict[str, Any], tuple[int, int, str]],
    ] = {}
    pair_bindings: dict[int, dict[str, Any]] = {}
    task_rows: list[tuple[int, dict[str, Any]]] = []
    task_metadata: dict[int, dict[str, Any]] = {}
    replays: dict[int, dict[str, Any]] = {}

    for source_index, original in indexed_annotated:
        annotated = dict(original)
        payload = {
            "static_eligibility": annotated.get("static_eligibility"),
            "structural_novelty": annotated.get("structural_novelty"),
            "structural_rejection": annotated.get("structural_rejection"),
        }
        _validate_annotation_payload(payload)
        static = annotated["static_eligibility"]
        if not static["eligible"]:
            outcomes[source_index] = ("rejected", annotated)
            continue
        audit = annotated["structural_novelty"]
        if not audit["novel"]:
            annotated["structural_rejection"] = "known_reference"
            outcomes[source_index] = ("rejected", annotated)
            continue

        key = (
            int(static["n"]),
            int(static["k"]),
            audit["canonical_digest"],
        )
        previous = representatives.get(key)
        if previous is None:
            representatives[key] = (source_index, annotated)
            outcomes[source_index] = ("kept", annotated)
            continue

        representative_index, representative = previous
        pair_input = _normalized_pair_input(annotated, representative)
        input_sha256 = _sha256_json(pair_input)
        pair_bindings[source_index] = {
            "schema_version": STRUCTURAL_PAIR_CACHE_SCHEMA_VERSION,
            "status": "COMPLETE",
            "input_sha256": input_sha256,
            "runtime_sha256": runtime_sha256,
            "candidate_input_sha256": structural_screen_input_sha256(
                annotated
            ),
            "representative_input_sha256": structural_screen_input_sha256(
                representative
            ),
            "representative_index": representative_index,
            "canonical_digest": key[2],
        }
        path = _pair_cache_path(cache_dir, input_sha256)
        entry = _read_pair_cache_entry(
            path,
            pair_input=pair_input,
            input_sha256=input_sha256,
            runtime_sha256=runtime_sha256,
        )
        pair_rows[source_index] = (annotated, representative, key)
        if entry is not None and entry["status"] == "complete":
            replays[source_index] = entry["replay"]
            continue
        attempts = 0 if entry is None else int(entry["attempt_count"])
        task_metadata[source_index] = {
            "pair_input": pair_input,
            "input_sha256": input_sha256,
            "path": path,
            "attempt_count": attempts + 1,
            "representative_index": representative_index,
            "canonical_digest": key[2],
        }
        task_rows.append((
            source_index,
            {
                "candidate": annotated,
                "representative": representative,
            },
        ))

    persisted_completed: set[int] = set()
    persisted_unresolved: set[int] = set()
    unresolved_evidence: list[dict[str, Any]] = []

    def persist_completed(
        index: int,
        replay: dict[str, Any],
    ) -> None:
        metadata = task_metadata[index]
        _validate_pair_replay_payload(
            replay,
            pair_input=metadata["pair_input"],
        )
        _write_pair_cache_entry(
            metadata["path"],
            pair_input=metadata["pair_input"],
            input_sha256=metadata["input_sha256"],
            runtime_sha256=runtime_sha256,
            status="complete",
            replay=replay,
            failure=None,
            attempt_count=metadata["attempt_count"],
        )
        replays[index] = replay
        persisted_completed.add(index)

    def persist_unresolved(
        index: int,
        failure: dict[str, Any],
    ) -> None:
        metadata = task_metadata[index]
        _write_pair_cache_entry(
            metadata["path"],
            pair_input=metadata["pair_input"],
            input_sha256=metadata["input_sha256"],
            runtime_sha256=runtime_sha256,
            status="unresolved",
            replay=None,
            failure=failure,
            attempt_count=metadata["attempt_count"],
        )
        unresolved_evidence.append({
            "operation": "within_pool_isomorphism",
            "candidate_index": index,
            "representative_index": metadata["representative_index"],
            "canonical_digest": metadata["canonical_digest"],
            "input_sha256": metadata["input_sha256"],
            "runtime_sha256": runtime_sha256,
            "candidate_input_sha256": structural_screen_input_sha256(
                pair_rows[index][0]
            ),
            "representative_input_sha256": structural_screen_input_sha256(
                pair_rows[index][1]
            ),
            "attempt_count": metadata["attempt_count"],
            "failure": copy.deepcopy(failure),
        })
        persisted_unresolved.add(index)

    if task_rows:
        completed, unresolved = _run_isomorphism_workers(
            task_rows,
            max_workers=max_workers,
            hard_timeout=hard_timeout,
            on_completed=persist_completed,
            on_unresolved=persist_unresolved,
        )
    else:
        completed, unresolved = {}, {}
    for index, replay in completed.items():
        if index not in persisted_completed:
            persist_completed(index, replay)
    for index, failure in unresolved.items():
        if index not in persisted_unresolved:
            persist_unresolved(index, failure)

    expected = set(task_metadata)
    observed = set(completed) | set(unresolved)
    if expected != observed or set(completed) & set(unresolved):
        raise StructuralScreenCacheError(
            "within-pool worker results are incomplete or duplicated"
        )

    for source_index, replay in replays.items():
        annotated, representative, key = pair_rows[source_index]
        audit = annotated["structural_novelty"]
        annotated["structural_novelty"] = {
            **audit,
            "novel": False,
            "relation": "within_run_css_tanner_permutation_equivalent",
            "matched_reference": representative.get("label") or (
                f"[[{representative.get('n')},{representative.get('k')},"
                f"{representative.get('d')}]]"
            ),
            "reference_digest": key[2],
            "explicit_isomorphism": copy.deepcopy(replay),
        }
        annotated["structural_rejection"] = "within_run_duplicate"
        annotated[STRUCTURAL_PAIR_REPLAY_FIELD] = copy.deepcopy(
            pair_bindings[source_index]
        )
        outcomes[source_index] = ("rejected", annotated)

    ordered_indexes = [index for index, _row in indexed_annotated]
    kept = [
        outcomes[index][1]
        for index in ordered_indexes
        if index in outcomes and outcomes[index][0] == "kept"
    ]
    rejected = [
        outcomes[index][1]
        for index in ordered_indexes
        if index in outcomes and outcomes[index][0] == "rejected"
    ]
    unresolved_evidence.sort(key=lambda item: item["candidate_index"])
    return kept, rejected, unresolved_evidence


def screen_css_results_with_deferred_cache(
    results: list[dict[str, Any]],
    *,
    cache_dir: Path,
    max_workers: int,
    hard_timeout: float = STRUCTURAL_SCREEN_HARD_TIMEOUT_SECONDS,
) -> tuple[list[dict], list[dict], list[dict[str, Any]]]:
    """Screen one ordered pool with every structural operation hard-walled."""

    indexed, annotation_unresolved = (
        _annotate_css_results_with_deferred_cache_indexed(
            results,
            cache_dir=cache_dir,
            max_workers=max_workers,
            hard_timeout=hard_timeout,
        )
    )
    kept, rejected, pair_unresolved = (
        _deduplicate_indexed_with_deferred_cache(
            indexed,
            cache_dir=cache_dir,
            max_workers=max_workers,
            hard_timeout=hard_timeout,
        )
    )
    unresolved_evidence = annotation_unresolved + pair_unresolved
    unresolved_evidence.sort(
        key=lambda item: (
            item["candidate_index"],
            item.get("operation", "candidate_annotation"),
        )
    )
    return kept, rejected, unresolved_evidence


def screen_css_results_with_cache(
    results: list[dict[str, Any]],
    *,
    cache_dir: Path,
    max_workers: int,
    hard_timeout: float = STRUCTURAL_SCREEN_HARD_TIMEOUT_SECONDS,
) -> tuple[list[dict], list[dict]]:
    """Strict wrapper that blocks when any structural screen is unresolved."""
    kept, rejected, unresolved = screen_css_results_with_deferred_cache(
        results,
        cache_dir=cache_dir,
        max_workers=max_workers,
        hard_timeout=hard_timeout,
    )
    if unresolved:
        raise StructuralScreenIncompleteError(unresolved)
    return kept, rejected
