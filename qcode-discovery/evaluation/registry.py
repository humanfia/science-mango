"""Versioned known-code registry with explicit construction replay.

Registry digests and ``(code_type, n, k)`` values are indexes only.  A code is
classified as known only after the indexed entry is reconstructed and an
explicit matrix permutation is replayed against the candidate.
"""

from __future__ import annotations

import hashlib
import json
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping

from evaluation.structural_dedup import canonical_digest
from evaluation.tanner_equivalence import (
    canonical_hash_noncss,
    replay_css_matrix_equivalence,
    replay_noncss_matrix_equivalence,
)


DEFAULT_REGISTRY = (
    Path(__file__).resolve().parent.parent / "results" / "known_code_registry.json"
)
REGISTRY_REPLAY_POLICY_SCHEMA_VERSION = 1
REGISTRY_REPLAY_POLICY = "explicit-construction-matrix-replay"
_HEX_DIGITS = frozenset("0123456789abcdef")


class _RegistryIntegrityError(ValueError):
    """An indexed registry entry contradicts its reconstructed construction."""


def canonical_digest_noncss(code) -> str:
    digest = hashlib.sha256()
    for left, right in canonical_hash_noncss(code):
        digest.update(int(left).to_bytes(4, "little"))
        digest.update(int(right).to_bytes(4, "little"))
    return digest.hexdigest()


def canonical_json_sha256(value: Any, *, omit: str | None = None) -> str:
    if isinstance(value, dict) and omit:
        value = {key: item for key, item in value.items() if key != omit}
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str)
        and len(value) == 64
        and all(character in _HEX_DIGITS for character in value)
    )


def _validate_registry_shape(registry: Any) -> dict[str, Any]:
    if not isinstance(registry, dict):
        raise ValueError("known-code registry must be an object")
    if registry.get("schema_version") != 1:
        raise ValueError("unsupported known-code registry schema")
    if not isinstance(registry.get("registry_version"), str):
        raise ValueError("known-code registry version is missing")
    entries = registry.get("entries")
    if not isinstance(entries, list):
        raise ValueError("known-code registry entries must be a list")
    identifiers: set[str] = set()
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            raise ValueError(f"known-code registry entry {index} is not an object")
        identifier = entry.get("id")
        if (
            not isinstance(identifier, str)
            or not identifier
            or identifier in identifiers
        ):
            raise ValueError(
                f"known-code registry entry {index} has an invalid or duplicate id"
            )
        identifiers.add(identifier)
        if entry.get("code_type") not in {"css", "noncss"}:
            raise ValueError(
                f"known-code registry entry {identifier} has invalid code_type"
            )
        if (
            type(entry.get("n")) is not int
            or entry["n"] <= 0
            or type(entry.get("k")) is not int
            or entry["k"] <= 0
            or not _is_sha256(entry.get("canonical_digest"))
            or not isinstance(entry.get("construction"), dict)
            or not isinstance(entry.get("family"), str)
            or not isinstance(entry.get("provenance"), list)
        ):
            raise ValueError(
                f"known-code registry entry {identifier} is malformed"
            )
    return registry


@lru_cache(maxsize=4)
def load_registry(path: str | Path = DEFAULT_REGISTRY) -> dict[str, Any]:
    registry = json.loads(Path(path).read_text())
    expected = canonical_json_sha256(registry, omit="registry_sha256")
    if registry.get("registry_sha256") != expected:
        raise ValueError("known-code registry SHA-256 mismatch")
    return _validate_registry_shape(registry)


def _replay_policy(
    *,
    indexed_entries: int,
    verified_entries: int,
    complete: bool,
) -> dict[str, Any]:
    return {
        "schema_version": REGISTRY_REPLAY_POLICY_SCHEMA_VERSION,
        "policy": REGISTRY_REPLAY_POLICY,
        "digest_terminal": False,
        "index_fields": [
            "code_type",
            "n",
            "k",
            "canonical_digest",
        ],
        "entry_construction_required": True,
        "explicit_matrix_replay_required": True,
        "indexed_entries": indexed_entries,
        "verified_entries": verified_entries,
        "complete": complete,
    }


def _incomplete_result(
    *,
    code_type: str,
    canonical_digest_value: str | None,
    registry: Mapping[str, Any] | None,
    indexed_entries: int,
    status: str,
    domain: str,
    code: str,
    detail: str,
    retryable: bool,
) -> dict[str, Any]:
    """Return non-terminal evidence for operational or integrity failures."""

    return {
        "status": status,
        "checked": False,
        "novel": None,
        "code_type": code_type,
        "canonical_digest": canonical_digest_value,
        "registry_version": (
            registry.get("registry_version")
            if isinstance(registry, Mapping)
            else None
        ),
        "registry_sha256": (
            registry.get("registry_sha256")
            if isinstance(registry, Mapping)
            else None
        ),
        "matched_entries": [],
        "replay_policy": _replay_policy(
            indexed_entries=indexed_entries,
            verified_entries=0,
            complete=False,
        ),
        "failure": {
            "domain": domain,
            "code": code,
            "detail": detail,
            "retryable": retryable,
            "terminal_candidate_rejection": False,
        },
    }


def _entry_construction(entry: Mapping[str, Any], code_type: str):
    construction = entry.get("construction")
    if not isinstance(construction, Mapping):
        raise _RegistryIntegrityError("entry construction is missing")
    expected_keys = (
        {"ell", "m", "A_terms", "B_terms"}
        if code_type == "css"
        else {"ell", "m", "A_terms", "B_terms", "C_terms", "D_terms"}
    )
    if set(construction) != expected_keys:
        raise _RegistryIntegrityError(
            "entry construction fields do not match its code type"
        )
    ell = construction.get("ell")
    m = construction.get("m")
    if (
        type(ell) is not int
        or ell <= 0
        or type(m) is not int
        or m <= 0
    ):
        raise _RegistryIntegrityError("entry lattice dimensions are invalid")
    try:
        normalized = {
            key: (
                int(value)
                if key in {"ell", "m"}
                else [tuple(term) for term in value]
            )
            for key, value in construction.items()
        }
        if code_type == "css":
            from evaluation.bb_code import build_bb_code

            return build_bb_code(**normalized)
        from evaluation.pbb_code import build_pbb_code

        code = build_pbb_code(**normalized)
        if not normalized["C_terms"] and not normalized["D_terms"]:
            raise _RegistryIntegrityError(
                "non-CSS registry entry has no perturbation"
            )
        return code
    except _RegistryIntegrityError:
        raise
    except (KeyError, TypeError, ValueError, OverflowError) as exc:
        raise _RegistryIntegrityError(
            "entry construction cannot be rebuilt"
        ) from exc


def _code_parameters(code) -> tuple[int, int]:
    n = int(code.num_qudits)
    k = int(code.dimension)
    if n <= 0 or k <= 0:
        raise ValueError("code has non-positive n or k")
    return n, k


def _replay_indexed_entry(
    candidate,
    entry: Mapping[str, Any],
    *,
    code_type: str,
    candidate_digest: str,
    candidate_n: int,
    candidate_k: int,
) -> dict[str, Any]:
    entry_code = _entry_construction(entry, code_type)
    try:
        entry_n, entry_k = _code_parameters(entry_code)
        entry_digest = (
            canonical_digest(entry_code)
            if code_type == "css"
            else canonical_digest_noncss(entry_code)
        )
    except (AttributeError, TypeError, ValueError, OverflowError) as exc:
        raise _RegistryIntegrityError(
            "entry construction has invalid reconstructed geometry"
        ) from exc
    if (
        type(entry.get("n")) is not int
        or type(entry.get("k")) is not int
        or entry_n != entry["n"]
        or entry_k != entry["k"]
        or entry_n != candidate_n
        or entry_k != candidate_k
        or not _is_sha256(entry.get("canonical_digest"))
        or entry_digest != entry["canonical_digest"]
        or entry_digest != candidate_digest
    ):
        raise _RegistryIntegrityError(
            "entry construction, digest, or n/k metadata is inconsistent"
        )
    replay = (
        replay_css_matrix_equivalence(candidate, entry_code)
        if code_type == "css"
        else replay_noncss_matrix_equivalence(candidate, entry_code)
    )
    if not isinstance(replay, Mapping) or replay.get("verified") is not True:
        raise _RegistryIntegrityError(
            "indexed digest match failed explicit matrix replay"
        )
    return {
        "id": entry["id"],
        "family": entry["family"],
        "provenance": entry["provenance"],
        "construction_sha256": canonical_json_sha256(entry["construction"]),
        "replay": dict(replay),
    }


def check_code_novelty(
    code,
    *,
    code_type: str,
    registry_path: str | Path = DEFAULT_REGISTRY,
) -> dict[str, Any]:
    """Check registry novelty with fail-closed explicit matrix replay.

    ``novel=False`` is emitted only for one or more fully replayed entries.
    Operational failures and registry contradictions return ``checked=False``,
    ``novel=None`` evidence so callers cannot cache them as known-code
    rejections.
    """

    if code_type not in {"css", "noncss"}:
        raise ValueError("code_type must be css or noncss")
    try:
        digest = (
            canonical_digest(code)
            if code_type == "css"
            else canonical_digest_noncss(code)
        )
        n, k = _code_parameters(code)
    except Exception as exc:
        return _incomplete_result(
            code_type=code_type,
            canonical_digest_value=None,
            registry=None,
            indexed_entries=0,
            status="INCOMPLETE",
            domain="runtime",
            code="CANDIDATE_CANONICALIZATION_FAILED",
            detail=str(exc),
            retryable=True,
        )

    try:
        registry = load_registry(Path(registry_path).resolve())
    except Exception as exc:
        return _incomplete_result(
            code_type=code_type,
            canonical_digest_value=digest,
            registry=None,
            indexed_entries=0,
            status="INCOMPLETE",
            domain="registry",
            code="REGISTRY_UNAVAILABLE_OR_INVALID",
            detail=str(exc),
            retryable=True,
        )
    matches = [
        entry for entry in registry["entries"]
        if entry["code_type"] == code_type
        and int(entry["n"]) == n
        and int(entry["k"]) == k
        and entry["canonical_digest"] == digest
    ]
    verified: list[dict[str, Any]] = []
    try:
        for entry in matches:
            verified.append(_replay_indexed_entry(
                code,
                entry,
                code_type=code_type,
                candidate_digest=digest,
                candidate_n=n,
                candidate_k=k,
            ))
    except _RegistryIntegrityError as exc:
        return _incomplete_result(
            code_type=code_type,
            canonical_digest_value=digest,
            registry=registry,
            indexed_entries=len(matches),
            status="EVIDENCE_CONTRADICTION",
            domain="registry",
            code="REGISTRY_ENTRY_REPLAY_CONTRADICTION",
            detail=str(exc),
            retryable=False,
        )
    except Exception as exc:
        return _incomplete_result(
            code_type=code_type,
            canonical_digest_value=digest,
            registry=registry,
            indexed_entries=len(matches),
            status="INCOMPLETE",
            domain="runtime",
            code="REGISTRY_ENTRY_REPLAY_FAILED",
            detail=str(exc),
            retryable=True,
        )
    return {
        "status": "COMPLETE",
        "checked": True,
        "novel": not verified,
        "code_type": code_type,
        "canonical_digest": digest,
        "registry_version": registry["registry_version"],
        "registry_sha256": registry["registry_sha256"],
        "matched_entries": verified,
        "replay_policy": _replay_policy(
            indexed_entries=len(matches),
            verified_entries=len(verified),
            complete=True,
        ),
    }
