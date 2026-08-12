"""Pure answer-blind candidate-to-result-contract transform.

This module intentionally depends only on the Python standard library until
the function's lazy Archon import.  It accepts caller-supplied JSON and has no
filesystem, environment, subprocess, or network input.
"""

from __future__ import annotations

import json


MAX_CANDIDATE_JSON_BYTES = 1_000_000


class BlindContractError(ValueError):
    """The supplied candidate cannot form a canonical result contract."""


def blind_contract_hashes(candidate_json: str, role: str) -> dict[str, str]:
    if role not in {"raw_result", "reported_result"}:
        raise BlindContractError("role must be raw_result or reported_result")
    encoded = candidate_json.encode("utf-8")
    if not encoded or len(encoded) > MAX_CANDIDATE_JSON_BYTES:
        raise BlindContractError("candidate_json is empty or exceeds the 1 MB limit")
    try:
        candidate = json.loads(candidate_json)
    except json.JSONDecodeError as exc:
        raise BlindContractError(
            f"candidate_json is invalid JSON: {exc.msg}"
        ) from exc
    if not isinstance(candidate, dict):
        raise BlindContractError("candidate_json must encode one JSON object")
    if candidate.get("official_answer_seen") is not False:
        raise BlindContractError(
            "answer-blind candidate must set official_answer_seen=false"
        )

    try:
        from archon.commands.loop.review_source_contract import (
            blind_result_payload_sha256,
            expected_nonnumeric_result_types,
            expected_numeric_result_types,
            lean_result_type_sha256,
        )
    except ImportError as exc:  # pragma: no cover - controller install defect
        raise BlindContractError(
            "answer-blind contract helper is unavailable"
        ) from exc

    if candidate.get("result_kind") == "numeric":
        expected = expected_numeric_result_types(candidate)
    elif candidate.get("result_kind") in {
        "symbolic",
        "classification",
        "underdetermined",
    }:
        expected = expected_nonnumeric_result_types(candidate)
    else:
        expected = None
    if expected is None or role not in expected:
        raise BlindContractError(
            "candidate fields do not determine an admissible answer-blind result contract"
        )
    expected_type = expected[role]
    return {
        "role": role,
        "expected_type": expected_type,
        "expected_type_sha256": lean_result_type_sha256(expected_type),
        "result_payload_sha256": blind_result_payload_sha256(candidate, role),
    }
