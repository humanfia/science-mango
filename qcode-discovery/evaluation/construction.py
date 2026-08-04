"""Authoritative dispatcher for compact CSS construction claims.

The adapter keeps historical BB claims replayable while adding the
source-bound ``coset-two-block-v1`` representation.  Packed matrices and
reported ``n``, ``k``, or distance values are never construction authority.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from hashlib import sha256
from numbers import Integral
from pathlib import Path
from typing import Any

from qldpc import codes

from evaluation.bb_code import build_bb_code, validate_terms
from evaluation.coset_two_block import (
    CONSTRUCTION_KIND as COSET_TWO_BLOCK_KIND,
    build_coset_two_block,
    normalize_coset_two_block_construction,
    symmetry_generator_proposals,
)
from evaluation.geometry import normalize_geometry


LEGACY_BB_KIND = "bb-v1"
_LEGACY_FIELDS = {"ell", "m", "A_terms", "B_terms", "geometry"}
_AMBIGUOUS_TOP_LEVEL_FIELDS = {
    "ell",
    "m",
    "A_terms",
    "B_terms",
    "geometry",
}


def _positive_int(value: Any, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise ValueError(f"{name} must be an integer")
    result = int(value)
    if result <= 0:
        raise ValueError(f"{name} must be positive")
    return result


def _terms(value: Any, *, ell: int, m: int, name: str) -> list[list[int]]:
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        raise ValueError(f"{name} must be a sequence of exponent pairs")
    normalized: list[list[int]] = []
    for index, term in enumerate(value):
        if (
            isinstance(term, (str, bytes))
            or not isinstance(term, Sequence)
            or len(term) != 2
        ):
            raise ValueError(f"{name}[{index}] must be an exponent pair")
        x_exp, y_exp = term
        if (
            isinstance(x_exp, bool)
            or not isinstance(x_exp, Integral)
            or isinstance(y_exp, bool)
            or not isinstance(y_exp, Integral)
        ):
            raise ValueError(f"{name}[{index}] exponents must be integers")
        normalized.append([int(x_exp), int(y_exp)])
    validate_terms(
        ell,
        m,
        [tuple(term) for term in normalized],
        name,
    )
    # Polynomial addition is commutative.  Sorting makes semantically equal
    # historical claims share the same construction identity.
    return sorted(normalized)


def _normalize_legacy_bb(value: Mapping[str, Any]) -> dict[str, Any]:
    actual = set(value)
    required = {"ell", "m", "A_terms", "B_terms"}
    unknown = actual - _LEGACY_FIELDS - {"kind"}
    missing = required - actual
    if missing or unknown:
        raise ValueError(
            "legacy BB construction fields do not match schema; "
            f"missing={sorted(missing)}, unknown={sorted(unknown)}"
        )
    if "kind" in value and value["kind"] != LEGACY_BB_KIND:
        raise ValueError(f"unsupported construction kind {value['kind']!r}")
    ell = _positive_int(value["ell"], name="ell")
    m = _positive_int(value["m"], name="m")
    geometry = normalize_geometry(ell, m, value.get("geometry"))
    normalized: dict[str, Any] = {
        "ell": ell,
        "m": m,
        "A_terms": _terms(value["A_terms"], ell=ell, m=m, name="A_terms"),
        "B_terms": _terms(value["B_terms"], ell=ell, m=m, name="B_terms"),
    }
    if geometry is not None:
        normalized["geometry"] = geometry
    return normalized


def _construction_payload(claim: Mapping[str, Any]) -> tuple[Mapping[str, Any], bool]:
    if not isinstance(claim, Mapping):
        raise ValueError("construction claim must be a mapping")
    if "construction" in claim:
        payload = claim["construction"]
        if not isinstance(payload, Mapping):
            raise ValueError("claim.construction must be a mapping")
        return payload, True
    return claim, False


def normalize_construction_claim(claim: Mapping[str, Any]) -> dict[str, Any]:
    """Return the canonical construction descriptor carried by ``claim``.

    A claim may either be the descriptor itself or contain it under the
    top-level ``construction`` field.  Non-construction result metadata is
    ignored.  A nested compact construction may not be accompanied by a
    second, conflicting top-level matrix/BB definition.
    """

    payload, nested = _construction_payload(claim)
    kind = payload.get("kind")
    if kind == COSET_TWO_BLOCK_KIND:
        if nested:
            ambiguous = sorted(set(claim) & _AMBIGUOUS_TOP_LEVEL_FIELDS)
            if ambiguous:
                raise ValueError(
                    "compact coset construction is ambiguous with top-level "
                    f"definition fields: {ambiguous}"
                )
        return normalize_coset_two_block_construction(payload)
    if kind not in {None, LEGACY_BB_KIND}:
        raise ValueError(f"unsupported construction kind {kind!r}")
    if nested:
        return _normalize_legacy_bb(payload)
    legacy_payload = {
        key: payload[key]
        for key in _LEGACY_FIELDS | {"kind"}
        if key in payload
    }
    return _normalize_legacy_bb(legacy_payload)


def construction_identity(claim: Mapping[str, Any]) -> dict[str, Any]:
    """Return the stable, JSON-safe semantic identity of a construction."""

    normalized = normalize_construction_claim(claim)
    if normalized.get("kind") == COSET_TWO_BLOCK_KIND:
        return dict(normalized)
    return {"kind": LEGACY_BB_KIND, **normalized}


def build_css_code_from_claim(claim: Mapping[str, Any]) -> codes.CSSCode:
    """Rebuild the authoritative CSS code encoded by a compact claim."""

    normalized = normalize_construction_claim(claim)
    if normalized.get("kind") == COSET_TWO_BLOCK_KIND:
        return build_coset_two_block(
            normalized["action_id"],
            normalized["left_support"],
            normalized["right_support"],
        )
    return build_bb_code(
        normalized["ell"],
        normalized["m"],
        [tuple(term) for term in normalized["A_terms"]],
        [tuple(term) for term in normalized["B_terms"]],
        geometry=normalized.get("geometry"),
    )


def candidate_symmetry_generators(claim: Mapping[str, Any]):
    """Return unverified construction-derived permutation proposals.

    The Stage-3 matrix replay is the sole authority for accepting these as
    automorphisms.  Legacy BB candidates currently expose no generic proposal
    through this dispatcher.
    """

    normalized = normalize_construction_claim(claim)
    if normalized.get("kind") != COSET_TWO_BLOCK_KIND:
        return ()
    return symmetry_generator_proposals(normalized)


def construction_source_fingerprint() -> str:
    """Hash every local source/data file that determines rebuilt matrices."""

    directory = Path(__file__).resolve().parent
    sources = (
        directory / "bb_code.py",
        directory / "geometry.py",
        directory / "coset_action_catalog.py",
        directory / "coset_two_block.py",
        directory / "coset_two_block_actions.v1.json",
        Path(__file__).resolve(),
    )
    digest = sha256()
    for path in sorted(sources, key=lambda item: item.name):
        payload = path.read_bytes()
        name = path.name.encode("utf-8")
        digest.update(len(name).to_bytes(4, "big"))
        digest.update(name)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return digest.hexdigest()


__all__ = [
    "COSET_TWO_BLOCK_KIND",
    "LEGACY_BB_KIND",
    "build_css_code_from_claim",
    "candidate_symmetry_generators",
    "construction_identity",
    "construction_source_fingerprint",
    "normalize_construction_claim",
]
