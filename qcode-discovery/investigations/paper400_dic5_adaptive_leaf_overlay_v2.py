#!/usr/bin/env python3
"""Authenticated, one-step adaptive refinement of one paper400 width-10 leaf.

This module is intentionally an overlay, not a solver runner and not a proof
artifact.  It first replays the complete root -> width-6 -> width-10 campaign,
then obtains the selected leaf through the width-10 module's same-process
verified-child API.  A full replay may be represented by an uncopyable,
non-serializable token bound to one active process/thread context, exact input
contents, external manifest pins, instance fingerprint, current sources, and
critical callable identities.  Such a token is revoked when its context exits.
It is a lifecycle/misuse boundary under an already authenticated code graph,
not a defense against arbitrary code execution inside the same Python process.
One externally pinned UNKNOWN/TIMEOUT evidence record may
authorize exactly one binary adaptive split.  Every non-conflicting child is
left PENDING.  Refining such a child requires a new hard-evidence record and a
new overlay chained to this one; this manifest never authorizes that work.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import threading
from collections.abc import Mapping, Sequence
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator

from investigations import paper400_dic5_adaptive_cnc_v2 as adaptive
from investigations import paper400_dic5_nested_width10_campaign_v1 as width10


width6 = width10.width6
hierarchy = width10.hierarchy
cube16 = width10.cube16
optimized = cube16.optimized
PROJECT = Path(__file__).resolve().parent.parent

SCHEMA_VERSION = 2
MANIFEST_KIND = "paper400-dic5-width10-adaptive-leaf-overlay-v2"
HARD_EVIDENCE_KIND = "paper400-dic5-width10-hard-leaf-evidence-v2"
VERIFICATION_KIND = "paper400-dic5-width10-adaptive-overlay-verification-v2"
AUTHORITY = "TEST_ONLY_ADAPTIVE_OVERLAY_V2"
COVER_FORMULATION = "one-authenticated-leaf-one-binary-pending-refinement-v2"
PHYSICAL_VARIABLE_MIN = 1
PHYSICAL_VARIABLE_MAX = 400
ONE_SPLIT_MAX_DEPTH = 1
ONE_SPLIT_MAX_NODES = 3
PENDING_STATUS = "PENDING"
PENDING_SOURCE = "generated-frontier-v1"
ALLOWED_HARD_STATUSES = frozenset({"TIMEOUT", "UNKNOWN"})

MANIFEST_FIELDS = frozenset({
    "schema_version",
    "manifest_kind",
    "cover_formulation",
    "authority",
    "test_only",
    "production_eligible",
    "launch_authorized",
    "publication_certificate",
    "ancestry",
    "parent_scope",
    "hard_evidence",
    "hard_evidence_sha256",
    "candidate_policy",
    "adaptive_manifest",
    "adaptive_manifest_sha256",
    "adaptive_verification",
    "descendants",
    "local_cover",
    "claim_scope",
    "source_binding",
    "solver_invoked",
    "manifest_sha256",
})

HARD_EVIDENCE_FIELDS = frozenset({
    "schema_version",
    "kind",
    "status",
    "width10_campaign_sha256",
    "global_leaf_index",
    "global_leaf_id",
    "leaf_sha256",
    "child_cnf_sha256",
    "child_dimacs_sha256",
    "combined_unit_clauses_sha256",
    "runner_record_sha256",
    "result_record_sha256",
    "timeout_policy",
    "hardness_only",
    "solver_terminal_claim",
    "evidence_sha256",
})

TIMEOUT_POLICY_FIELDS = frozenset({
    "timeout_seconds",
    "elapsed_seconds",
    "timed_out",
    "status_elapsed_consistent",
    "interpretation",
})

DESCENDANT_FIELDS = frozenset({
    "schema_version",
    "descendant_index",
    "descendant_id",
    "adaptive_node_id",
    "adaptive_node_sha256",
    "path",
    "depth",
    "parent_leaf_sha256",
    "adaptive_manifest_sha256",
    "decision_literal",
    "relative_assignment_literals",
    "relative_unit_clauses",
    "relative_unit_clauses_sha256",
    "combined_unit_clauses",
    "combined_unit_clauses_sha256",
    "child_cnf_sha256",
    "child_dimacs_sha256",
    "child_num_variables",
    "child_num_clauses",
    "child_dimacs_bytes",
    "bcp",
    "observed_status",
    "status_source",
    "terminal_reason",
    "pending",
    "solver_terminal_authenticated",
    "descendant_sha256",
})

VERIFICATION_FIELDS = frozenset({
    "schema_version",
    "kind",
    "valid",
    "overlay_manifest_sha256",
    "expected_overlay_sha256",
    "hard_evidence_sha256",
    "expected_hard_evidence_sha256",
    "width10_campaign_sha256",
    "global_leaf_index",
    "adaptive_manifest_sha256",
    "descendant_count",
    "pending_count",
    "bcp_conflict_count",
    "mutually_exclusive",
    "exhaustive",
    "parent_formula_equivalence_certified",
    "current_source_exact_replay",
    "test_only",
    "production_eligible",
    "launch_authorized",
    "publication_certificate",
    "record_sha256",
})


class AdaptiveLeafOverlayError(RuntimeError):
    """An ancestry, evidence, physical-variable, cover, or hash is invalid."""


_CAMPAIGN_REPLAY_AUTHORITY = object()
_ACTIVE_CAMPAIGN_REPLAYS: dict[
    tuple[int, threading.Thread], tuple[Any, object]
] = {}


class _CampaignReplayToken:
    """Opaque witness valid only while its issuing context is active."""

    __slots__ = (
        "_authority", "_active_nonce", "_active", "_pid", "_thread",
        "_width10_campaign", "_width6_campaign", "_parent_manifest",
        "_instance", "_strict_base", "_expected_pins", "_input_bytes",
        "_instance_fingerprint", "_source_binding_bytes",
        "_callable_snapshot", "_verification", "_verification_bytes",
        "_sealed",
    )

    def __init__(
        self, authority: object, *, active_nonce: object,
        width10_campaign: Mapping[str, Any],
        width6_campaign: Mapping[str, Any],
        parent_manifest: Mapping[str, Any],
        instance: Any, strict_base: bool,
        expected_pins: tuple[str, str, str],
        input_bytes: tuple[bytes, bytes, bytes],
        instance_fingerprint: bytes,
        source_binding_bytes: bytes,
        callable_snapshot: tuple[Any, ...],
        verification: dict[str, Any],
    ) -> None:
        if authority is not _CAMPAIGN_REPLAY_AUTHORITY:
            raise AdaptiveLeafOverlayError(
                "campaign replay token constructor is private"
            )
        object.__setattr__(self, "_authority", authority)
        object.__setattr__(self, "_active_nonce", active_nonce)
        object.__setattr__(self, "_active", True)
        object.__setattr__(self, "_pid", os.getpid())
        object.__setattr__(self, "_thread", threading.current_thread())
        object.__setattr__(self, "_width10_campaign", width10_campaign)
        object.__setattr__(self, "_width6_campaign", width6_campaign)
        object.__setattr__(self, "_parent_manifest", parent_manifest)
        object.__setattr__(self, "_instance", instance)
        object.__setattr__(self, "_strict_base", strict_base)
        object.__setattr__(self, "_expected_pins", expected_pins)
        object.__setattr__(self, "_input_bytes", input_bytes)
        object.__setattr__(
            self, "_instance_fingerprint", instance_fingerprint
        )
        object.__setattr__(
            self, "_source_binding_bytes", source_binding_bytes
        )
        object.__setattr__(self, "_callable_snapshot", callable_snapshot)
        object.__setattr__(self, "_verification", verification)
        object.__setattr__(
            self, "_verification_bytes", canonical_bytes(verification)
        )
        object.__setattr__(self, "_sealed", True)

    def __setattr__(self, name: str, value: Any) -> None:
        del name, value
        raise TypeError("campaign replay token is immutable")

    def __copy__(self) -> Any:
        raise TypeError("campaign replay token is non-copyable")

    def __deepcopy__(self, memo: Any) -> Any:
        del memo
        raise TypeError("campaign replay token is non-copyable")

    def __reduce__(self) -> Any:
        raise TypeError("campaign replay token is non-serializable")

    def __reduce_ex__(self, protocol: int) -> Any:
        del protocol
        raise TypeError("campaign replay token is non-serializable")

    def __getstate__(self) -> Any:
        raise TypeError("campaign replay token has no serializable state")

    def __repr__(self) -> str:
        state = "active" if self._active else "revoked"
        return f"<campaign-replay-token {state}>"


def _require_strict_json(value: Any, *, label: str = "value") -> None:
    """Reject Python values that JSON would silently coerce or normalize."""

    value_type = type(value)
    if value is None or value_type in (str, bool, int):
        return
    if value_type is float:
        if not math.isfinite(value):
            raise AdaptiveLeafOverlayError(f"{label} contains a non-finite float")
        return
    if value_type is list:
        for index, item in enumerate(value):
            _require_strict_json(item, label=f"{label}[{index}]")
        return
    if value_type is dict:
        for key, item in value.items():
            if type(key) is not str:
                raise AdaptiveLeafOverlayError(f"{label} has a non-string key")
            _require_strict_json(item, label=f"{label}.{key}")
        return
    raise AdaptiveLeafOverlayError(
        f"{label} contains non-JSON type {value_type.__name__}"
    )


def canonical_bytes(value: Any) -> bytes:
    _require_strict_json(value)
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise AdaptiveLeafOverlayError(f"not canonical JSON: {exc}") from exc


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(
    value: Mapping[str, Any], field: str = "manifest_sha256",
) -> dict[str, Any]:
    if type(value) is not dict or field in value:
        raise AdaptiveLeafOverlayError("invalid value passed to seal")
    _require_strict_json(value)
    result = dict(value)
    result[field] = canonical_sha256(result)
    return result


def _is_sha256(value: Any) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        return bytes.fromhex(value).hex() == value
    except ValueError:
        return False


def selfhash_valid(value: Any, field: str = "manifest_sha256") -> bool:
    if type(value) is not dict or not _is_sha256(value.get(field)):
        return False
    unsigned = dict(value)
    stored = unsigned.pop(field)
    try:
        return stored == canonical_sha256(unsigned)
    except AdaptiveLeafOverlayError:
        return False


def json_type_equal(left: Any, right: Any) -> bool:
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(
            json_type_equal(left[key], right[key]) for key in left
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            json_type_equal(a, b)
            for a, b in zip(left, right, strict=True)
        )
    return bool(left == right)


def _require_sha256(value: Any, *, label: str) -> str:
    if not _is_sha256(value):
        raise AdaptiveLeafOverlayError(f"{label} is not a canonical SHA-256")
    return value


def _campaign_callable_snapshot() -> tuple[Any, ...]:
    modules = (adaptive, width10, width6, hierarchy, cube16, optimized)
    functions = (
        width10.verify_campaign_manifest,
        width10._validate_fast_boundary,
        width10.verified_child_dimacs_from_verification,
        width10._source_binding,
        width10._selected_parent_binding,
        width10._width6_campaign_binding,
        width10._nested_leaf_record,
        width10._local_cover_record,
        width10.selfhash_valid,
        width10.json_type_equal,
        width6._parent_cover_binding,
        cube16._strict_base_failures,
        cube16._cnf_sha256,
        optimized._array_sha256,
        optimized.canonical_sha256,
        adaptive.parse_dimacs,
        adaptive.deterministic_bcp,
        adaptive.render_cube_dimacs,
        adaptive.build_adaptive_manifest,
        adaptive.verify_adaptive_manifest,
        _source_binding,
        _campaign_replay_verification,
        build_overlay_manifest,
        verify_overlay_manifest,
    )
    records: list[tuple[Any, ...]] = []
    for function in functions:
        kwdefaults = function.__kwdefaults__
        records.append((
            function,
            function.__code__,
            function.__defaults__,
            kwdefaults,
            b"" if kwdefaults is None else canonical_bytes(kwdefaults),
            function.__module__,
            function.__qualname__,
            function.__code__.co_filename,
        ))
    return modules, tuple(records)


def _same_callable_snapshot(
    observed: tuple[Any, ...], expected: tuple[Any, ...],
) -> bool:
    if (
        type(observed) is not tuple
        or type(expected) is not tuple
        or len(observed) != 2
        or len(expected) != 2
    ):
        return False
    observed_modules, observed_records = observed
    expected_modules, expected_records = expected
    if (
        type(observed_modules) is not tuple
        or type(expected_modules) is not tuple
        or len(observed_modules) != len(expected_modules)
        or any(
            left is not right
            for left, right in zip(
                observed_modules, expected_modules, strict=True
            )
        )
        or type(observed_records) is not tuple
        or type(expected_records) is not tuple
        or len(observed_records) != len(expected_records)
    ):
        return False
    for left, right in zip(
        observed_records, expected_records, strict=True
    ):
        if (
            type(left) is not tuple
            or type(right) is not tuple
            or len(left) != 8
            or len(right) != 8
            or any(left[index] is not right[index] for index in range(4))
            or left[4:] != right[4:]
        ):
            return False
    return True


def _campaign_source_snapshot() -> bytes:
    return canonical_bytes({
        "overlay": _source_binding(),
        "width10": width10._source_binding(),
    })


def _instance_replay_fingerprint(
    instance: Any, *, strict_base: bool,
) -> bytes:
    if type(instance) is not optimized.OptimizedInstance:
        raise AdaptiveLeafOverlayError(
            "campaign replay instance has the wrong exact type"
        )
    if type(instance.cnf) is not dict or type(instance.report) is not dict:
        raise AdaptiveLeafOverlayError(
            "campaign replay instance payload is malformed"
        )
    if type(instance.dimacs) is not bytes:
        raise AdaptiveLeafOverlayError(
            "campaign replay instance DIMACS is not bytes"
        )
    cnf = instance.cnf
    try:
        recomputed_cnf = cube16._cnf_sha256(
            num_variables=cnf["num_variables"],
            clauses=cnf["clauses"],
            native_atmost=cnf["native_atmost"],
        )
    except (KeyError, TypeError, ValueError) as exc:
        raise AdaptiveLeafOverlayError(
            f"campaign replay CNF fingerprint failed: {exc}"
        ) from exc
    if cnf.get("cnf_sha256") != recomputed_cnf:
        raise AdaptiveLeafOverlayError(
            "campaign replay CNF self-binding mismatch"
        )
    report_unsigned = dict(instance.report)
    report_hash = report_unsigned.pop("report_sha256", None)
    if (
        not _is_sha256(report_hash)
        or optimized.canonical_sha256(report_unsigned) != report_hash
    ):
        raise AdaptiveLeafOverlayError(
            "campaign replay instance report self-hash mismatch"
        )
    if strict_base and cube16._strict_base_failures(instance):
        raise AdaptiveLeafOverlayError(
            "campaign replay instance fails strict base validation"
        )
    matrices = (
        ("hx", "checks", instance.hx),
        ("hz", "checks", instance.hz),
        ("lx", "logicals", instance.lx),
        ("lz", "logicals", instance.lz),
        ("basis_checks", "checks", instance.basis_checks),
        ("active_logical", "logicals", instance.active_logical),
    )
    matrix_records = []
    for role, kind, matrix in matrices:
        try:
            shape = [int(value) for value in matrix.shape]
            digest = optimized._array_sha256(kind, matrix)
            raw_digest = hashlib.sha256(
                matrix.tobytes(order="C")
            ).hexdigest()
        except (AttributeError, TypeError, ValueError) as exc:
            raise AdaptiveLeafOverlayError(
                f"campaign replay matrix fingerprint failed for {role}: {exc}"
            ) from exc
        matrix_records.append({
            "role": role,
            "shape": shape,
            "dtype": str(matrix.dtype),
            "semantic_sha256": digest,
            "raw_sha256": raw_digest,
        })
    return canonical_bytes({
        "instance_type_module": type(instance).__module__,
        "instance_type_qualname": type(instance).__qualname__,
        "cnf_canonical_sha256": optimized.canonical_sha256(cnf),
        "cnf_recomputed_sha256": recomputed_cnf,
        "dimacs_sha256": hashlib.sha256(instance.dimacs).hexdigest(),
        "dimacs_bytes": len(instance.dimacs),
        "report_canonical_sha256": optimized.canonical_sha256(
            instance.report
        ),
        "report_sha256": report_hash,
        "matrices": matrix_records,
        "strict_base": strict_base,
    })


def _campaign_input_snapshot(
    width10_campaign: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any, *, strict_base: bool,
) -> tuple[
    tuple[bytes, bytes, bytes], bytes, bytes, tuple[Any, ...]
]:
    return (
        (
            canonical_bytes(width10_campaign),
            canonical_bytes(width6_campaign),
            canonical_bytes(parent_manifest),
        ),
        _instance_replay_fingerprint(
            instance, strict_base=strict_base
        ),
        _campaign_source_snapshot(),
        _campaign_callable_snapshot(),
    )


def _poison_campaign_replay(token: Any) -> None:
    if type(token) is _CampaignReplayToken:
        try:
            object.__setattr__(token, "_active", False)
        except (AttributeError, TypeError):
            pass


def _close_campaign_replay(
    token: _CampaignReplayToken, active_nonce: object,
) -> None:
    try:
        key = (token._pid, token._thread)
        registered = _ACTIVE_CAMPAIGN_REPLAYS.get(key)
        if (
            registered is not None
            and registered[0] is token
            and registered[1] is active_nonce
        ):
            _ACTIVE_CAMPAIGN_REPLAYS.pop(key, None)
    finally:
        object.__setattr__(token, "_active", False)
        object.__setattr__(token, "_active_nonce", None)
        object.__setattr__(token, "_pid", -1)
        object.__setattr__(token, "_thread", None)
        object.__setattr__(token, "_width10_campaign", None)
        object.__setattr__(token, "_width6_campaign", None)
        object.__setattr__(token, "_parent_manifest", None)
        object.__setattr__(token, "_instance", None)
        object.__setattr__(token, "_strict_base", None)
        object.__setattr__(token, "_expected_pins", ())
        object.__setattr__(token, "_input_bytes", ())
        object.__setattr__(token, "_instance_fingerprint", b"")
        object.__setattr__(token, "_source_binding_bytes", b"")
        object.__setattr__(token, "_callable_snapshot", ())
        object.__setattr__(token, "_verification", None)
        object.__setattr__(token, "_verification_bytes", b"")


@contextmanager
def acquire_campaign_replay_token(
    width10_campaign: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    expected_width10_campaign_sha256: str,
    expected_width6_campaign_sha256: str,
    expected_parent_manifest_sha256: str,
    parent_cube_index: int = width10.TARGET_PARENT_CUBE_INDEX,
    strict_base: bool = True,
) -> Iterator[_CampaignReplayToken]:
    """Yield one owner-bound full-replay witness, then revoke it."""

    if type(strict_base) is not bool:
        raise AdaptiveLeafOverlayError(
            "strict_base must be a strict boolean"
        )
    if (
        type(parent_cube_index) is not int
        or parent_cube_index != width10.TARGET_PARENT_CUBE_INDEX
    ):
        raise AdaptiveLeafOverlayError(
            "campaign replay token has the wrong parent cube"
        )
    expected_pins = (
        _require_sha256(
            expected_width10_campaign_sha256,
            label="expected_width10_campaign_sha256",
        ),
        _require_sha256(
            expected_width6_campaign_sha256,
            label="expected_width6_campaign_sha256",
        ),
        _require_sha256(
            expected_parent_manifest_sha256,
            label="expected_parent_manifest_sha256",
        ),
    )
    inputs = (width10_campaign, width6_campaign, parent_manifest)
    for value, expected, label in zip(
        inputs,
        expected_pins,
        ("width10 campaign", "width6 campaign", "parent manifest"),
        strict=True,
    ):
        if (
            type(value) is not dict
            or value.get("manifest_sha256") != expected
            or not selfhash_valid(value)
        ):
            raise AdaptiveLeafOverlayError(
                f"{label} misses its external SHA-256 pin"
            )
    key = (os.getpid(), threading.current_thread())
    if key in _ACTIVE_CAMPAIGN_REPLAYS:
        raise AdaptiveLeafOverlayError(
            "nested campaign replay contexts are forbidden"
        )
    before = _campaign_input_snapshot(
        width10_campaign,
        width6_campaign,
        parent_manifest,
        instance,
        strict_base=strict_base,
    )
    try:
        verification = width10.verify_campaign_manifest(
            width10_campaign,
            width6_campaign,
            parent_manifest,
            instance,
            parent_cube_index=parent_cube_index,
            strict_base=strict_base,
        )
    except (
        width10.NestedWidth10CampaignError,
        width6.WidenedParentCampaignError,
        hierarchy.HierarchicalCubeError,
        cube16.Cube16Error,
        IndexError,
        KeyError,
        TypeError,
        ValueError,
    ) as exc:
        raise AdaptiveLeafOverlayError(
            f"width10 full replay failed: {exc}"
        ) from exc
    if (
        type(verification) is not dict
        or verification.get("valid") is not True
        or verification.get("mutually_exclusive") is not True
        or verification.get("exhaustive") is not True
        or verification.get(
            "parent000_formula_equivalence_certified"
        ) is not True
    ):
        raise AdaptiveLeafOverlayError(
            "width10 full replay did not certify the campaign"
        )
    after = _campaign_input_snapshot(
        width10_campaign,
        width6_campaign,
        parent_manifest,
        instance,
        strict_base=strict_base,
    )
    if (
        before[:3] != after[:3]
        or not _same_callable_snapshot(before[3], after[3])
    ):
        raise AdaptiveLeafOverlayError(
            "campaign replay inputs changed during full verification"
        )
    active_nonce = object()
    token = _CampaignReplayToken(
        _CAMPAIGN_REPLAY_AUTHORITY,
        active_nonce=active_nonce,
        width10_campaign=width10_campaign,
        width6_campaign=width6_campaign,
        parent_manifest=parent_manifest,
        instance=instance,
        strict_base=strict_base,
        expected_pins=expected_pins,
        input_bytes=before[0],
        instance_fingerprint=before[1],
        source_binding_bytes=before[2],
        callable_snapshot=before[3],
        verification=verification,
    )
    _ACTIVE_CAMPAIGN_REPLAYS[key] = (token, active_nonce)
    try:
        yield token
    finally:
        _close_campaign_replay(token, active_nonce)


def _campaign_replay_verification(
    token: Any,
    width10_campaign: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any, *, strict_base: bool,
) -> dict[str, Any]:
    if type(token) is not _CampaignReplayToken:
        raise AdaptiveLeafOverlayError(
            "campaign replay token has the wrong exact type"
        )
    try:
        key = (os.getpid(), threading.current_thread())
        registered = _ACTIVE_CAMPAIGN_REPLAYS.get(key)
        if (
            token._authority is not _CAMPAIGN_REPLAY_AUTHORITY
            or token._active is not True
            or token._pid != os.getpid()
            or token._thread is not threading.current_thread()
            or registered is None
            or registered[0] is not token
            or registered[1] is not token._active_nonce
            or token._width10_campaign is not width10_campaign
            or token._width6_campaign is not width6_campaign
            or token._parent_manifest is not parent_manifest
            or token._instance is not instance
            or type(strict_base) is not bool
            or token._strict_base is not strict_base
        ):
            raise AdaptiveLeafOverlayError(
                "campaign replay token owner/input binding mismatch"
            )
        current = _campaign_input_snapshot(
            width10_campaign,
            width6_campaign,
            parent_manifest,
            instance,
            strict_base=strict_base,
        )
        if (
            current[0] != token._input_bytes
            or current[1] != token._instance_fingerprint
            or current[2] != token._source_binding_bytes
            or not _same_callable_snapshot(
                current[3], token._callable_snapshot
            )
            or tuple(
                value.get("manifest_sha256")
                for value in (
                    width10_campaign, width6_campaign, parent_manifest
                )
            ) != token._expected_pins
            or canonical_bytes(token._verification)
            != token._verification_bytes
        ):
            raise AdaptiveLeafOverlayError(
                "campaign replay token content binding mismatch"
            )
        try:
            verification = json.loads(
                token._verification_bytes.decode("ascii")
            )
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise AdaptiveLeafOverlayError(
                "campaign replay token payload is malformed"
            ) from exc
        width10._validate_fast_boundary(
            width10_campaign,
            width6_campaign,
            parent_manifest,
            verification_record=verification,
            parent_cube_index=width10.TARGET_PARENT_CUBE_INDEX,
            strict_base=strict_base,
        )
        after = _campaign_input_snapshot(
            width10_campaign,
            width6_campaign,
            parent_manifest,
            instance,
            strict_base=strict_base,
        )
        if (
            after[:3] != current[:3]
            or not _same_callable_snapshot(after[3], current[3])
        ):
            raise AdaptiveLeafOverlayError(
                "campaign replay inputs changed during fast-boundary use"
            )
        return verification
    except AdaptiveLeafOverlayError:
        _poison_campaign_replay(token)
        raise
    except Exception as exc:
        _poison_campaign_replay(token)
        raise AdaptiveLeafOverlayError(
            f"campaign replay token validation failed: {exc}"
        ) from exc


def _require_plain_dict(value: Any, *, label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise AdaptiveLeafOverlayError(f"{label} must be a plain object")
    _require_strict_json(value, label=label)
    return value


def _candidate_tuple(candidate_variables: Sequence[int]) -> tuple[int, ...]:
    if type(candidate_variables) not in (list, tuple):
        raise AdaptiveLeafOverlayError(
            "candidate_variables must be a list or tuple of physical DIMACS variables"
        )
    candidates: set[int] = set()
    for variable in candidate_variables:
        if (
            type(variable) is not int
            or not PHYSICAL_VARIABLE_MIN <= variable <= PHYSICAL_VARIABLE_MAX
        ):
            raise AdaptiveLeafOverlayError(
                "candidate variable must be a strict integer in physical range 1..400"
            )
        if variable in candidates:
            raise AdaptiveLeafOverlayError("candidate variables contain a duplicate")
        candidates.add(variable)
    if not candidates:
        raise AdaptiveLeafOverlayError("at least one candidate variable is required")
    return tuple(sorted(candidates))


def _validate_timeout_policy(policy: Any, *, status: str) -> None:
    if type(policy) is not dict or set(policy) != TIMEOUT_POLICY_FIELDS:
        raise AdaptiveLeafOverlayError("timeout policy field set mismatch")
    _require_strict_json(policy, label="timeout_policy")
    timeout_seconds = policy["timeout_seconds"]
    elapsed_seconds = policy["elapsed_seconds"]
    timed_out = policy["timed_out"]
    if type(timeout_seconds) is not float or not timeout_seconds > 0.0:
        raise AdaptiveLeafOverlayError("timeout_seconds must be a positive finite float")
    if type(elapsed_seconds) is not float or elapsed_seconds < 0.0:
        raise AdaptiveLeafOverlayError("elapsed_seconds must be a nonnegative finite float")
    if type(timed_out) is not bool:
        raise AdaptiveLeafOverlayError("timed_out must be a strict boolean")
    expected_consistency = bool(
        (status == "TIMEOUT" and timed_out and elapsed_seconds >= timeout_seconds)
        or (status == "UNKNOWN" and not timed_out)
    )
    if policy["status_elapsed_consistent"] is not True or not expected_consistency:
        raise AdaptiveLeafOverlayError("hard status is inconsistent with timeout/elapsed data")
    if policy["interpretation"] != "hardness-observation-not-terminal-proof-v2":
        raise AdaptiveLeafOverlayError("timeout policy interpretation mismatch")


def _validate_hard_evidence(evidence: Any) -> dict[str, Any]:
    evidence = _require_plain_dict(evidence, label="hard_evidence")
    if set(evidence) != HARD_EVIDENCE_FIELDS:
        raise AdaptiveLeafOverlayError("hard evidence field set mismatch")
    if evidence.get("schema_version") != SCHEMA_VERSION:
        raise AdaptiveLeafOverlayError("hard evidence schema mismatch")
    if evidence.get("kind") != HARD_EVIDENCE_KIND:
        raise AdaptiveLeafOverlayError("hard evidence kind mismatch")
    if evidence.get("status") not in ALLOWED_HARD_STATUSES:
        raise AdaptiveLeafOverlayError("hard evidence status must be TIMEOUT or UNKNOWN")
    if type(evidence.get("global_leaf_index")) is not int:
        raise AdaptiveLeafOverlayError("hard evidence leaf index must be a strict integer")
    if type(evidence.get("global_leaf_id")) is not str:
        raise AdaptiveLeafOverlayError("hard evidence leaf id must be a string")
    for field in (
        "width10_campaign_sha256",
        "leaf_sha256",
        "child_cnf_sha256",
        "child_dimacs_sha256",
        "combined_unit_clauses_sha256",
        "runner_record_sha256",
        "result_record_sha256",
        "evidence_sha256",
    ):
        _require_sha256(evidence.get(field), label=f"hard evidence {field}")
    if evidence.get("hardness_only") is not True:
        raise AdaptiveLeafOverlayError("hard evidence must be hardness-only")
    if evidence.get("solver_terminal_claim") is not False:
        raise AdaptiveLeafOverlayError("hard evidence cannot claim a solver terminal")
    _validate_timeout_policy(evidence.get("timeout_policy"), status=evidence["status"])
    if not selfhash_valid(evidence, "evidence_sha256"):
        raise AdaptiveLeafOverlayError("hard evidence self-hash mismatch")
    return evidence


def build_hard_evidence_record(
    width10_campaign: Mapping[str, Any],
    *,
    global_leaf_index: int,
    status: str,
    runner_record_sha256: str,
    result_record_sha256: str,
    timeout_seconds: float,
    elapsed_seconds: float,
    timed_out: bool,
) -> dict[str, Any]:
    """Build an integrity-sealed observation; overlay verification supplies trust."""

    campaign = _require_plain_dict(width10_campaign, label="width10_campaign")
    if (
        type(global_leaf_index) is not int
        or not 0 <= global_leaf_index < width10.LEAF_COUNT
    ):
        raise AdaptiveLeafOverlayError("global_leaf_index must be a strict integer in 0..1023")
    if type(status) is not str or status not in ALLOWED_HARD_STATUSES:
        raise AdaptiveLeafOverlayError("status must be exactly TIMEOUT or UNKNOWN")
    for value, label in (
        (runner_record_sha256, "runner_record_sha256"),
        (result_record_sha256, "result_record_sha256"),
    ):
        _require_sha256(value, label=label)
    if type(timeout_seconds) is not float or not math.isfinite(timeout_seconds):
        raise AdaptiveLeafOverlayError("timeout_seconds must be a finite float")
    if type(elapsed_seconds) is not float or not math.isfinite(elapsed_seconds):
        raise AdaptiveLeafOverlayError("elapsed_seconds must be a finite float")
    if type(timed_out) is not bool:
        raise AdaptiveLeafOverlayError("timed_out must be a strict boolean")
    leaves = campaign.get("leaves")
    if type(leaves) is not list or len(leaves) != width10.LEAF_COUNT:
        raise AdaptiveLeafOverlayError("width10 campaign leaf table is malformed")
    leaf = leaves[global_leaf_index]
    if type(leaf) is not dict:
        raise AdaptiveLeafOverlayError("selected width10 leaf is malformed")
    timeout_policy = {
        "timeout_seconds": timeout_seconds,
        "elapsed_seconds": elapsed_seconds,
        "timed_out": timed_out,
        "status_elapsed_consistent": True,
        "interpretation": "hardness-observation-not-terminal-proof-v2",
    }
    _validate_timeout_policy(timeout_policy, status=status)
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": HARD_EVIDENCE_KIND,
        "status": status,
        "width10_campaign_sha256": campaign.get("manifest_sha256"),
        "global_leaf_index": global_leaf_index,
        "global_leaf_id": leaf.get("global_leaf_id"),
        "leaf_sha256": leaf.get("leaf_sha256"),
        "child_cnf_sha256": leaf.get("child_cnf_sha256"),
        "child_dimacs_sha256": leaf.get("child_dimacs_sha256"),
        "combined_unit_clauses_sha256": leaf.get(
            "combined_unit_clauses_sha256"
        ),
        "runner_record_sha256": runner_record_sha256,
        "result_record_sha256": result_record_sha256,
        "timeout_policy": timeout_policy,
        "hardness_only": True,
        "solver_terminal_claim": False,
    }, "evidence_sha256")


def _source_binding() -> dict[str, Any]:
    sources = {
        "adaptive_leaf_overlay_v2_source": Path(__file__).resolve(),
        "generic_adaptive_core_source": Path(adaptive.__file__).resolve(),
        "nested_width10_campaign_source": Path(width10.__file__).resolve(),
        "width6_campaign_source": Path(width6.__file__).resolve(),
        "hierarchical_refiner_source": Path(hierarchy.__file__).resolve(),
        "root_cover_source": Path(cube16.__file__).resolve(),
        "optimized_builder_source": Path(optimized.__file__).resolve(),
    }
    records: list[dict[str, Any]] = []
    for role, path in sorted(sources.items()):
        try:
            relative = path.relative_to(PROJECT).as_posix()
        except ValueError as exc:
            raise AdaptiveLeafOverlayError(f"source escapes project: {role}") from exc
        records.append({
            "role": role,
            "relative_path": relative,
            "sha256": cube16._file_sha256(path),
        })
    return seal({
        "schema_version": SCHEMA_VERSION,
        "method": "fresh-current-source-sha256-exact-replay-v2",
        "sources": records,
        "source_role_sequence_sha256": canonical_sha256([
            record["role"] for record in records
        ]),
    }, "source_binding_sha256")


def _canonical_object_binding(value: Mapping[str, Any]) -> dict[str, Any]:
    payload = canonical_bytes(value)
    return {
        "manifest_sha256": value.get("manifest_sha256"),
        "canonical_json_sha256": hashlib.sha256(payload).hexdigest(),
        "canonical_json_bytes": len(payload),
    }


def _ancestry_binding(
    width10_campaign: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    leaf: Mapping[str, Any],
    campaign_verification: Mapping[str, Any],
) -> dict[str, Any]:
    parent_index = leaf["parent_cube_index"]
    width6_leaf_index = leaf["width6_leaf_index"]
    root_parent = parent_manifest["cubes"][parent_index]
    old_leaf = width6_campaign["leaves"][width6_leaf_index]
    root = seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": parent_manifest.get("manifest_kind"),
        **_canonical_object_binding(parent_manifest),
        "base_cnf_sha256": parent_manifest.get("base", {}).get("cnf_sha256"),
        "base_dimacs_sha256": parent_manifest.get("base", {}).get(
            "dimacs_sha256"
        ),
        "parent_cube_index": parent_index,
        "parent_cube_id": root_parent.get("cube_id"),
        "parent_cube_sha256": root_parent.get("cube_sha256"),
        "parent_cube_cnf_sha256": root_parent.get("cube_cnf_sha256"),
        "parent_cube_dimacs_sha256": root_parent.get("cube_dimacs_sha256"),
    }, "root_ancestry_sha256")
    widened = seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": width6_campaign.get("manifest_kind"),
        **_canonical_object_binding(width6_campaign),
        "parent_cover_manifest_sha256": width6_campaign.get(
            "parent_cover", {}
        ).get("manifest_sha256"),
        "selected_parent_binding_sha256": width6_campaign.get(
            "selected_parent", {}
        ).get("selected_parent_binding_sha256"),
        "refinement_manifest_sha256": width6_campaign.get(
            "refinement", {}
        ).get("manifest_sha256"),
        "width6_leaf_index": width6_leaf_index,
        "width6_leaf_id": old_leaf.get("leaf_id"),
        "width6_leaf_sha256": old_leaf.get("leaf_sha256"),
        "width6_child_id": old_leaf.get("child_id"),
        "width6_child_sha256": old_leaf.get("child_sha256"),
        "width6_child_cnf_sha256": old_leaf.get("child_cnf_sha256"),
        "width6_child_dimacs_sha256": old_leaf.get("child_dimacs_sha256"),
    }, "width6_ancestry_sha256")
    nested = seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": width10_campaign.get("manifest_kind"),
        **_canonical_object_binding(width10_campaign),
        "width6_campaign_manifest_sha256": width10_campaign.get(
            "width6_campaign", {}
        ).get("manifest_sha256"),
        "width6_campaign_binding_sha256": canonical_sha256(
            width10_campaign.get("width6_campaign")
        ),
        "selected_parent_binding_sha256": width10_campaign.get(
            "selected_parent", {}
        ).get("selected_parent_binding_sha256"),
        "global_leaf_index": leaf.get("global_leaf_index"),
        "global_leaf_id": leaf.get("global_leaf_id"),
        "leaf_sha256": leaf.get("leaf_sha256"),
        "child_cnf_sha256": leaf.get("child_cnf_sha256"),
        "child_dimacs_sha256": leaf.get("child_dimacs_sha256"),
        "full_verification_record_sha256": campaign_verification.get(
            "record_sha256"
        ),
    }, "width10_ancestry_sha256")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "chain": [root, widened, nested],
        "chain_roles": ["root-width4", "selected-width6", "selected-width10-leaf"],
        "chain_hash_sequence_sha256": canonical_sha256([
            root["root_ancestry_sha256"],
            widened["width6_ancestry_sha256"],
            nested["width10_ancestry_sha256"],
        ]),
    }, "ancestry_sha256")


def _validated_parent_payload(
    leaf: Mapping[str, Any], payload: bytes,
) -> tuple[dict[str, Any], list[list[int]], dict[str, Any], list[int]]:
    if type(payload) is not bytes:
        raise AdaptiveLeafOverlayError("verified child API did not return bytes")
    parsed = adaptive.parse_dimacs(payload)
    if hashlib.sha256(payload).hexdigest() != leaf.get("child_dimacs_sha256"):
        raise AdaptiveLeafOverlayError("verified child DIMACS SHA-256 mismatch")
    if len(payload) != leaf.get("child_dimacs_bytes"):
        raise AdaptiveLeafOverlayError("verified child DIMACS byte count mismatch")
    if parsed["num_variables"] != leaf.get("child_num_variables"):
        raise AdaptiveLeafOverlayError("verified child variable count mismatch")
    if parsed["num_clauses"] != leaf.get("child_num_clauses"):
        raise AdaptiveLeafOverlayError("verified child clause count mismatch")
    structured_hash = cube16._cnf_sha256(
        num_variables=parsed["num_variables"],
        clauses=parsed["clauses"],
        native_atmost=None,
    )
    if structured_hash != leaf.get("child_cnf_sha256"):
        raise AdaptiveLeafOverlayError("verified child structured CNF SHA-256 mismatch")
    units = leaf.get("combined_unit_clauses")
    if type(units) is not list or not units:
        raise AdaptiveLeafOverlayError("selected leaf combined units are malformed")
    normalized_units: list[list[int]] = []
    unit_variables: set[int] = set()
    for clause in units:
        if (
            type(clause) is not list
            or len(clause) != 1
            or type(clause[0]) is not int
            or not PHYSICAL_VARIABLE_MIN <= abs(clause[0]) <= PHYSICAL_VARIABLE_MAX
        ):
            raise AdaptiveLeafOverlayError(
                "selected leaf units must be singleton physical DIMACS literals"
            )
        variable = abs(clause[0])
        if variable in unit_variables:
            raise AdaptiveLeafOverlayError("selected leaf reassigns a physical variable")
        unit_variables.add(variable)
        normalized_units.append([clause[0]])
    if canonical_sha256(normalized_units) != leaf.get("combined_unit_clauses_sha256"):
        raise AdaptiveLeafOverlayError("selected leaf combined-unit hash mismatch")
    if parsed["clauses"][-len(normalized_units):] != normalized_units:
        raise AdaptiveLeafOverlayError("selected leaf units are not the exact DIMACS suffix")
    parent_bcp = adaptive.deterministic_bcp(payload, ())
    if parent_bcp.get("conflict") is not False:
        raise AdaptiveLeafOverlayError("hard parent leaf is already a BCP conflict")
    assignment = parent_bcp.get("assignment")
    if type(assignment) is not list:
        raise AdaptiveLeafOverlayError("parent BCP assignment is malformed")
    fixed_variables: list[int] = []
    for record in assignment:
        if (
            type(record) is not dict
            or set(record) != {"dimacs_variable", "value"}
            or type(record["dimacs_variable"]) is not int
            or type(record["value"]) is not int
            or record["value"] not in (0, 1)
        ):
            raise AdaptiveLeafOverlayError("parent BCP assignment record is malformed")
        fixed_variables.append(record["dimacs_variable"])
    if fixed_variables != sorted(set(fixed_variables)):
        raise AdaptiveLeafOverlayError("parent BCP fixed variables are not canonical")
    return parsed, normalized_units, parent_bcp, fixed_variables


def _validate_one_split(
    adaptive_manifest: Mapping[str, Any], *,
    expected_parent_dimacs_sha256: str,
    expected_candidates: Sequence[int],
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if type(adaptive_manifest) is not dict:
        raise AdaptiveLeafOverlayError("adaptive manifest is malformed")
    if adaptive_manifest.get("test_only") is not True:
        raise AdaptiveLeafOverlayError("adaptive core material is not test-only")
    if adaptive_manifest.get("production_eligible") is not False:
        raise AdaptiveLeafOverlayError("adaptive core claims production eligibility")
    if adaptive_manifest.get("launch_authorized") is not False:
        raise AdaptiveLeafOverlayError("adaptive core claims launch authorization")
    source = adaptive_manifest.get("source")
    policy = adaptive_manifest.get("policy")
    tree = adaptive_manifest.get("tree")
    if not all(type(section) is dict for section in (source, policy, tree)):
        raise AdaptiveLeafOverlayError("adaptive manifest sections are malformed")
    if source.get("source_cnf_sha256") != expected_parent_dimacs_sha256:
        raise AdaptiveLeafOverlayError("adaptive source is not the authenticated parent DIMACS")
    if policy.get("candidate_variables") != list(expected_candidates):
        raise AdaptiveLeafOverlayError("adaptive candidate policy mismatch")
    if policy.get("max_depth") != ONE_SPLIT_MAX_DEPTH:
        raise AdaptiveLeafOverlayError("adaptive overlay must use max_depth one")
    if policy.get("max_nodes") != ONE_SPLIT_MAX_NODES:
        raise AdaptiveLeafOverlayError("adaptive overlay must use exactly a three-node budget")
    nodes = tree.get("nodes")
    covers = tree.get("local_covers")
    if type(nodes) is not list or len(nodes) != 3:
        raise AdaptiveLeafOverlayError("adaptive overlay must contain exactly three nodes")
    if type(covers) is not list or len(covers) != 1:
        raise AdaptiveLeafOverlayError("adaptive overlay must contain exactly one local cover")
    if any(type(node) is not dict for node in nodes):
        raise AdaptiveLeafOverlayError("adaptive node is malformed")
    by_id = {node.get("node_id"): node for node in nodes}
    if len(by_id) != 3 or any(type(node_id) is not str for node_id in by_id):
        raise AdaptiveLeafOverlayError("adaptive node ids are malformed or duplicated")
    root_id = tree.get("root_node_id")
    root = by_id.get(root_id)
    if root is None:
        raise AdaptiveLeafOverlayError("adaptive root is missing")
    selected = root.get("selected_variable")
    if (
        root.get("path") != "R"
        or root.get("depth") != 0
        or root.get("assumptions") != []
        or root.get("observed_status") not in ALLOWED_HARD_STATUSES
        or root.get("status_source") != "caller-observation-v2"
        or root.get("terminal_reason") is not None
        or type(selected) is not int
        or selected not in expected_candidates
        or not PHYSICAL_VARIABLE_MIN <= selected <= PHYSICAL_VARIABLE_MAX
    ):
        raise AdaptiveLeafOverlayError("adaptive root does not encode one hard physical split")
    positive = by_id.get(root.get("positive_child_id"))
    negative = by_id.get(root.get("negative_child_id"))
    if positive is None or negative is None or positive is negative:
        raise AdaptiveLeafOverlayError("adaptive root children are missing or aliased")
    expected_children = (
        (positive, "R+", selected),
        (negative, "R-", -selected),
    )
    for child, path, literal in expected_children:
        if (
            child.get("path") != path
            or child.get("depth") != 1
            or child.get("parent_node_id") != root_id
            or child.get("parent_cube_sha256") != root.get("cube_sha256")
            or child.get("edge_literal") != literal
            or child.get("assumptions") != [literal]
            or child.get("selected_variable") is not None
            or child.get("positive_child_id") is not None
            or child.get("negative_child_id") is not None
        ):
            raise AdaptiveLeafOverlayError("adaptive child edge/assumption binding mismatch")
        if child.get("bcp", {}).get("conflict") is True:
            if (
                child.get("observed_status") != adaptive.BCP_CONFLICT_STATUS
                or child.get("status_source") != "deterministic-bcp-v2"
                or child.get("terminal_reason") != "BCP_CONFLICT"
            ):
                raise AdaptiveLeafOverlayError("BCP-conflict child status mismatch")
        elif (
            child.get("observed_status") != PENDING_STATUS
            or child.get("status_source") != PENDING_SOURCE
            or child.get("terminal_reason") != PENDING_STATUS
        ):
            raise AdaptiveLeafOverlayError(
                "every non-conflicting generated child must stop at PENDING"
            )
    cover = covers[0]
    if (
        type(cover) is not dict
        or cover.get("parent_node_id") != root_id
        or cover.get("parent_path") != "R"
        or cover.get("parent_cube_sha256") != root.get("cube_sha256")
        or cover.get("split_variable") != selected
        or cover.get("positive_child", {}).get("node_id") != positive.get("node_id")
        or cover.get("positive_child", {}).get("decision_literal") != selected
        or cover.get("negative_child", {}).get("node_id") != negative.get("node_id")
        or cover.get("negative_child", {}).get("decision_literal") != -selected
        or cover.get("mutually_exclusive") is not True
        or cover.get("exhaustive") is not True
    ):
        raise AdaptiveLeafOverlayError("adaptive local binary cover is incomplete")
    return root, [positive, negative]


def _descendant_record(
    *,
    descendant_index: int,
    node: Mapping[str, Any],
    parent_payload: bytes,
    parent_leaf: Mapping[str, Any],
    parent_units: Sequence[Sequence[int]],
    adaptive_manifest_sha256: str,
) -> dict[str, Any]:
    assumptions = node.get("assumptions")
    if type(assumptions) is not list or len(assumptions) != 1:
        raise AdaptiveLeafOverlayError("adaptive descendant is not one relative literal")
    literal = assumptions[0]
    relative_units = [[literal]]
    combined_units = [list(clause) for clause in parent_units] + relative_units
    payload = adaptive.render_cube_dimacs(parent_payload, assumptions)
    parsed = adaptive.parse_dimacs(payload)
    structured_hash = cube16._cnf_sha256(
        num_variables=parsed["num_variables"],
        clauses=parsed["clauses"],
        native_atmost=None,
    )
    conflict = node.get("bcp", {}).get("conflict") is True
    pending = not conflict
    return seal({
        "schema_version": SCHEMA_VERSION,
        "descendant_index": descendant_index,
        "descendant_id": (
            f"{parent_leaf['global_leaf_id']}-adaptive-{descendant_index}"
        ),
        "adaptive_node_id": node.get("node_id"),
        "adaptive_node_sha256": node.get("node_sha256"),
        "path": node.get("path"),
        "depth": node.get("depth"),
        "parent_leaf_sha256": parent_leaf.get("leaf_sha256"),
        "adaptive_manifest_sha256": adaptive_manifest_sha256,
        "decision_literal": literal,
        "relative_assignment_literals": [literal],
        "relative_unit_clauses": relative_units,
        "relative_unit_clauses_sha256": canonical_sha256(relative_units),
        "combined_unit_clauses": combined_units,
        "combined_unit_clauses_sha256": canonical_sha256(combined_units),
        "child_cnf_sha256": structured_hash,
        "child_dimacs_sha256": hashlib.sha256(payload).hexdigest(),
        "child_num_variables": parsed["num_variables"],
        "child_num_clauses": parsed["num_clauses"],
        "child_dimacs_bytes": len(payload),
        "bcp": node.get("bcp"),
        "observed_status": node.get("observed_status"),
        "status_source": node.get("status_source"),
        "terminal_reason": node.get("terminal_reason"),
        "pending": pending,
        "solver_terminal_authenticated": False,
    }, "descendant_sha256")


def _local_cover_record(
    parent_leaf: Mapping[str, Any],
    root: Mapping[str, Any],
    descendants: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    positive, negative = descendants
    split_variable = root["selected_variable"]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "method": "independent-one-variable-Boolean-cover-v2",
        "identity": "P <=> (P AND v) OR (P AND NOT v)",
        "parent_global_leaf_index": parent_leaf.get("global_leaf_index"),
        "parent_leaf_sha256": parent_leaf.get("leaf_sha256"),
        "parent_child_cnf_sha256": parent_leaf.get("child_cnf_sha256"),
        "parent_child_dimacs_sha256": parent_leaf.get("child_dimacs_sha256"),
        "split_variable": split_variable,
        "positive_descendant_sha256": positive.get("descendant_sha256"),
        "positive_decision_literal": split_variable,
        "negative_descendant_sha256": negative.get("descendant_sha256"),
        "negative_decision_literal": -split_variable,
        "descendant_sha256_sequence_sha256": canonical_sha256([
            descendant.get("descendant_sha256") for descendant in descendants
        ]),
        "descendant_count": 2,
        "mutually_exclusive": True,
        "exhaustive": True,
        "parent_formula_equivalence_certified": True,
        "proof_method": "Boolean-complement-case-split-checked-from-relative-units-v2",
    }, "local_cover_sha256")


def _independent_local_cover_checks(manifest: Mapping[str, Any]) -> None:
    parent = manifest.get("parent_scope")
    descendants = manifest.get("descendants")
    cover = manifest.get("local_cover")
    if type(parent) is not dict or type(descendants) is not list or type(cover) is not dict:
        raise AdaptiveLeafOverlayError("overlay local-cover sections are malformed")
    if len(descendants) != 2 or any(type(item) is not dict for item in descendants):
        raise AdaptiveLeafOverlayError("overlay must contain exactly two descendants")
    if [item.get("descendant_index") for item in descendants] != [0, 1]:
        raise AdaptiveLeafOverlayError("overlay descendants are missing, duplicated, or reordered")
    if any(set(item) != DESCENDANT_FIELDS for item in descendants):
        raise AdaptiveLeafOverlayError("descendant field set mismatch")
    if any(not selfhash_valid(item, "descendant_sha256") for item in descendants):
        raise AdaptiveLeafOverlayError("descendant self-hash mismatch")
    split = cover.get("split_variable")
    if type(split) is not int or not PHYSICAL_VARIABLE_MIN <= split <= PHYSICAL_VARIABLE_MAX:
        raise AdaptiveLeafOverlayError("local-cover split variable is not physical")
    expected_literals = [split, -split]
    parent_units = parent.get("combined_unit_clauses")
    if type(parent_units) is not list:
        raise AdaptiveLeafOverlayError("parent unit clauses are malformed")
    for descendant, literal in zip(descendants, expected_literals, strict=True):
        relative_units = [[literal]]
        combined_units = parent_units + relative_units
        if (
            descendant.get("decision_literal") != literal
            or descendant.get("relative_assignment_literals") != [literal]
            or descendant.get("relative_unit_clauses") != relative_units
            or descendant.get("relative_unit_clauses_sha256")
            != canonical_sha256(relative_units)
            or descendant.get("combined_unit_clauses") != combined_units
            or descendant.get("combined_unit_clauses_sha256")
            != canonical_sha256(combined_units)
            or descendant.get("parent_leaf_sha256") != parent.get("leaf_sha256")
            or descendant.get("adaptive_manifest_sha256")
            != manifest.get("adaptive_manifest_sha256")
        ):
            raise AdaptiveLeafOverlayError("descendant relative-unit cover binding mismatch")
        if descendant.get("bcp", {}).get("conflict") is not True and (
            descendant.get("observed_status") != PENDING_STATUS
            or descendant.get("status_source") != PENDING_SOURCE
            or descendant.get("terminal_reason") != PENDING_STATUS
            or descendant.get("pending") is not True
        ):
            raise AdaptiveLeafOverlayError("non-conflicting descendant is not PENDING")
    if (
        not selfhash_valid(cover, "local_cover_sha256")
        or cover.get("parent_leaf_sha256") != parent.get("leaf_sha256")
        or cover.get("positive_descendant_sha256")
        != descendants[0].get("descendant_sha256")
        or cover.get("positive_decision_literal") != split
        or cover.get("negative_descendant_sha256")
        != descendants[1].get("descendant_sha256")
        or cover.get("negative_decision_literal") != -split
        or cover.get("descendant_count") != 2
        or cover.get("mutually_exclusive") is not True
        or cover.get("exhaustive") is not True
        or cover.get("parent_formula_equivalence_certified") is not True
    ):
        raise AdaptiveLeafOverlayError("independent local-cover certificate mismatch")


def build_overlay_manifest(
    width10_campaign: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    global_leaf_index: int,
    hard_evidence: Mapping[str, Any],
    expected_hard_evidence_sha256: str,
    candidate_variables: Sequence[int],
    strict_base: bool = True,
    _campaign_replay_token: Any | None = None,
) -> dict[str, Any]:
    """Build one evidence-bounded split below one fully authenticated leaf."""

    if type(strict_base) is not bool:
        raise AdaptiveLeafOverlayError("strict_base must be a strict boolean")
    if (
        type(global_leaf_index) is not int
        or not 0 <= global_leaf_index < width10.LEAF_COUNT
    ):
        raise AdaptiveLeafOverlayError("global_leaf_index must be a strict integer in 0..1023")
    candidates = _candidate_tuple(candidate_variables)
    expected_evidence_hash = _require_sha256(
        expected_hard_evidence_sha256,
        label="expected_hard_evidence_sha256",
    )
    evidence = _validate_hard_evidence(hard_evidence)
    if evidence["evidence_sha256"] != expected_evidence_hash:
        raise AdaptiveLeafOverlayError("hard evidence does not match external SHA-256 pin")

    try:
        if _campaign_replay_token is None:
            campaign_verification = width10.verify_campaign_manifest(
                width10_campaign,
                width6_campaign,
                parent_manifest,
                instance,
                parent_cube_index=width10.TARGET_PARENT_CUBE_INDEX,
                strict_base=strict_base,
            )
            if (
                campaign_verification.get("valid") is not True
                or campaign_verification.get("mutually_exclusive") is not True
                or campaign_verification.get("exhaustive") is not True
                or campaign_verification.get(
                    "parent000_formula_equivalence_certified"
                ) is not True
            ):
                raise AdaptiveLeafOverlayError(
                    "width10 full replay did not certify the campaign"
                )
        else:
            campaign_verification = _campaign_replay_verification(
                _campaign_replay_token,
                width10_campaign,
                width6_campaign,
                parent_manifest,
                instance,
                strict_base=strict_base,
            )
        parent_payload = width10.verified_child_dimacs_from_verification(
            width10_campaign,
            width6_campaign,
            parent_manifest,
            instance,
            verification_record=campaign_verification,
            global_leaf_index=global_leaf_index,
            parent_cube_index=width10.TARGET_PARENT_CUBE_INDEX,
            strict_base=strict_base,
        )
    except AdaptiveLeafOverlayError:
        raise
    except (
        width10.NestedWidth10CampaignError,
        width6.WidenedParentCampaignError,
        hierarchy.HierarchicalCubeError,
        cube16.Cube16Error,
        IndexError,
        KeyError,
        TypeError,
        ValueError,
    ) as exc:
        raise AdaptiveLeafOverlayError(f"width10 leaf authentication failed: {exc}") from exc

    leaf = width10_campaign["leaves"][global_leaf_index]
    if type(leaf) is not dict or not width10.selfhash_valid(leaf, "leaf_sha256"):
        raise AdaptiveLeafOverlayError("selected width10 leaf self-hash mismatch")
    evidence_bindings = {
        "width10_campaign_sha256": width10_campaign.get("manifest_sha256"),
        "global_leaf_index": global_leaf_index,
        "global_leaf_id": leaf.get("global_leaf_id"),
        "leaf_sha256": leaf.get("leaf_sha256"),
        "child_cnf_sha256": leaf.get("child_cnf_sha256"),
        "child_dimacs_sha256": leaf.get("child_dimacs_sha256"),
        "combined_unit_clauses_sha256": leaf.get(
            "combined_unit_clauses_sha256"
        ),
    }
    for field, expected in evidence_bindings.items():
        if evidence.get(field) != expected:
            raise AdaptiveLeafOverlayError(f"hard evidence {field} binds the wrong leaf")

    parsed, parent_units, parent_bcp, fixed_variables = _validated_parent_payload(
        leaf, parent_payload
    )
    unit_variables = sorted(abs(clause[0]) for clause in parent_units)
    forbidden = set(unit_variables) | set(fixed_variables)
    overlap = sorted(set(candidates) & forbidden)
    if overlap:
        raise AdaptiveLeafOverlayError(
            f"candidate variables are already fixed by units or BCP: {overlap}"
        )

    try:
        adaptive_manifest = adaptive.build_adaptive_manifest(
            parent_payload,
            parent_cube=(),
            candidate_variables=candidates,
            status_by_path={"R": evidence["status"]},
            max_depth=ONE_SPLIT_MAX_DEPTH,
            max_nodes=ONE_SPLIT_MAX_NODES,
        )
        adaptive_verification = adaptive.verify_adaptive_manifest(
            adaptive_manifest,
            parent_payload,
            expected_manifest_sha256=adaptive_manifest["manifest_sha256"],
        )
    except (adaptive.AdaptiveCubeError, KeyError, TypeError, ValueError) as exc:
        raise AdaptiveLeafOverlayError(f"adaptive core replay failed: {exc}") from exc
    if adaptive_verification.get("valid") is not True:
        raise AdaptiveLeafOverlayError("adaptive core verification was not valid")
    root, child_nodes = _validate_one_split(
        adaptive_manifest,
        expected_parent_dimacs_sha256=hashlib.sha256(parent_payload).hexdigest(),
        expected_candidates=candidates,
    )
    descendants = [
        _descendant_record(
            descendant_index=index,
            node=node,
            parent_payload=parent_payload,
            parent_leaf=leaf,
            parent_units=parent_units,
            adaptive_manifest_sha256=adaptive_manifest["manifest_sha256"],
        )
        for index, node in enumerate(child_nodes)
    ]
    local_cover = _local_cover_record(leaf, root, descendants)
    pending_count = sum(item["pending"] is True for item in descendants)
    conflict_count = sum(item["bcp"]["conflict"] is True for item in descendants)
    if pending_count + conflict_count != 2:
        raise AdaptiveLeafOverlayError("adaptive frontier contains an unauthorized status")

    parent_scope = seal({
        "schema_version": SCHEMA_VERSION,
        "global_leaf_index": global_leaf_index,
        "global_leaf_id": leaf.get("global_leaf_id"),
        "leaf_sha256": leaf.get("leaf_sha256"),
        "child_cnf_sha256": leaf.get("child_cnf_sha256"),
        "child_dimacs_sha256": leaf.get("child_dimacs_sha256"),
        "child_num_variables": parsed["num_variables"],
        "child_num_clauses": parsed["num_clauses"],
        "child_dimacs_bytes": len(parent_payload),
        "combined_unit_clauses": parent_units,
        "combined_unit_clauses_sha256": canonical_sha256(parent_units),
        "verified_child_payload_sha256": hashlib.sha256(parent_payload).hexdigest(),
        "verified_child_payload_bytes": len(parent_payload),
        "parent_bcp": parent_bcp,
        "parent_bcp_fixed_variables": fixed_variables,
        "parent_bcp_fixed_variables_sha256": canonical_sha256(fixed_variables),
    }, "parent_scope_sha256")
    ancestry = _ancestry_binding(
        width10_campaign,
        width6_campaign,
        parent_manifest,
        leaf,
        campaign_verification,
    )
    candidate_policy = seal({
        "schema_version": SCHEMA_VERSION,
        "physical_dimacs_variable_min": PHYSICAL_VARIABLE_MIN,
        "physical_dimacs_variable_max": PHYSICAL_VARIABLE_MAX,
        "candidate_variables": list(candidates),
        "candidate_variables_sha256": canonical_sha256(list(candidates)),
        "excluded_combined_unit_variables": unit_variables,
        "excluded_parent_bcp_fixed_variables": fixed_variables,
        "selected_variable": root["selected_variable"],
        "hard_evidence_records_consumed": 1,
        "authorized_split_count": 1,
        "max_depth": ONE_SPLIT_MAX_DEPTH,
        "max_nodes": ONE_SPLIT_MAX_NODES,
        "nonconflicting_generated_status": PENDING_STATUS,
        "descendant_refinement_authorized": False,
        "next_round_requires_new_hard_evidence": True,
        "next_round_requires_prior_overlay_hash_chain": True,
        "fixed_multi-level-lookahead_authorized": False,
    }, "candidate_policy_sha256")
    manifest = seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": MANIFEST_KIND,
        "cover_formulation": COVER_FORMULATION,
        "authority": AUTHORITY,
        "test_only": True,
        "production_eligible": False,
        "launch_authorized": False,
        "publication_certificate": False,
        "ancestry": ancestry,
        "parent_scope": parent_scope,
        "hard_evidence": dict(evidence),
        "hard_evidence_sha256": evidence["evidence_sha256"],
        "candidate_policy": candidate_policy,
        "adaptive_manifest": adaptive_manifest,
        "adaptive_manifest_sha256": adaptive_manifest["manifest_sha256"],
        "adaptive_verification": adaptive_verification,
        "descendants": descendants,
        "local_cover": local_cover,
        "claim_scope": {
            "root_width6_width10_ancestry_authenticated": True,
            "base_cnf_changed": False,
            "only_one_physical_operator_unit_clause_added_per_descendant": True,
            "parent_leaf_formula_equivalence_certified": True,
            "hard_evidence_is_not_a_terminal_solver_claim": True,
            "adaptive_frontier_is_not_classified": True,
            "this_overlay_proves_parent_unsat": False,
            "this_overlay_proves_distance_lower_bound": False,
            "further_refinement_requires_new_evidence_and_overlay": True,
        },
        "source_binding": _source_binding(),
        "solver_invoked": False,
    })
    _independent_local_cover_checks(manifest)
    if _campaign_replay_token is not None:
        _campaign_replay_verification(
            _campaign_replay_token,
            width10_campaign,
            width6_campaign,
            parent_manifest,
            instance,
            strict_base=strict_base,
        )
    return manifest


def verify_overlay_manifest(
    manifest: Mapping[str, Any],
    width10_campaign: Mapping[str, Any],
    width6_campaign: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: Any,
    *,
    global_leaf_index: int,
    hard_evidence: Mapping[str, Any],
    expected_hard_evidence_sha256: str,
    candidate_variables: Sequence[int],
    expected_overlay_sha256: str,
    strict_base: bool = True,
    _campaign_replay_token: Any | None = None,
) -> dict[str, Any]:
    """Independently check the local cover and perform exact current-source replay."""

    raw = _require_plain_dict(manifest, label="overlay_manifest")
    if set(raw) != MANIFEST_FIELDS:
        raise AdaptiveLeafOverlayError("overlay manifest field set mismatch")
    if not selfhash_valid(raw):
        raise AdaptiveLeafOverlayError("overlay manifest self-hash mismatch")
    overlay_pin = _require_sha256(
        expected_overlay_sha256, label="expected_overlay_sha256"
    )
    if raw["manifest_sha256"] != overlay_pin:
        raise AdaptiveLeafOverlayError("overlay manifest does not match external SHA-256 pin")
    if (
        raw.get("schema_version") != SCHEMA_VERSION
        or raw.get("manifest_kind") != MANIFEST_KIND
        or raw.get("cover_formulation") != COVER_FORMULATION
        or raw.get("authority") != AUTHORITY
        or raw.get("test_only") is not True
        or raw.get("production_eligible") is not False
        or raw.get("launch_authorized") is not False
        or raw.get("publication_certificate") is not False
        or raw.get("solver_invoked") is not False
    ):
        raise AdaptiveLeafOverlayError("overlay authority or claim-scope flags mismatch")
    evidence_pin = _require_sha256(
        expected_hard_evidence_sha256,
        label="expected_hard_evidence_sha256",
    )
    supplied_evidence = _validate_hard_evidence(hard_evidence)
    if supplied_evidence["evidence_sha256"] != evidence_pin:
        raise AdaptiveLeafOverlayError("supplied hard evidence misses external pin")
    if raw.get("hard_evidence_sha256") != evidence_pin:
        raise AdaptiveLeafOverlayError("overlay hard-evidence hash binding mismatch")
    if not json_type_equal(raw.get("hard_evidence"), supplied_evidence):
        raise AdaptiveLeafOverlayError("embedded hard evidence differs from caller evidence")

    _independent_local_cover_checks(raw)
    expected = build_overlay_manifest(
        width10_campaign,
        width6_campaign,
        parent_manifest,
        instance,
        global_leaf_index=global_leaf_index,
        hard_evidence=supplied_evidence,
        expected_hard_evidence_sha256=evidence_pin,
        candidate_variables=candidate_variables,
        strict_base=strict_base,
        _campaign_replay_token=_campaign_replay_token,
    )
    if not json_type_equal(raw, expected):
        raise AdaptiveLeafOverlayError(
            "overlay differs from fresh current-source type-exact replay"
        )
    descendants = raw["descendants"]
    pending_count = sum(item["pending"] is True for item in descendants)
    conflict_count = sum(item["bcp"]["conflict"] is True for item in descendants)
    record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": VERIFICATION_KIND,
        "valid": True,
        "overlay_manifest_sha256": raw["manifest_sha256"],
        "expected_overlay_sha256": overlay_pin,
        "hard_evidence_sha256": raw["hard_evidence_sha256"],
        "expected_hard_evidence_sha256": evidence_pin,
        "width10_campaign_sha256": width10_campaign.get("manifest_sha256"),
        "global_leaf_index": global_leaf_index,
        "adaptive_manifest_sha256": raw["adaptive_manifest_sha256"],
        "descendant_count": len(descendants),
        "pending_count": pending_count,
        "bcp_conflict_count": conflict_count,
        "mutually_exclusive": True,
        "exhaustive": True,
        "parent_formula_equivalence_certified": True,
        "current_source_exact_replay": True,
        "test_only": True,
        "production_eligible": False,
        "launch_authorized": False,
        "publication_certificate": False,
    }, "record_sha256")
    if _campaign_replay_token is not None:
        _campaign_replay_verification(
            _campaign_replay_token,
            width10_campaign,
            width6_campaign,
            parent_manifest,
            instance,
            strict_base=strict_base,
        )
    return record


__all__ = [
    "ALLOWED_HARD_STATUSES",
    "AUTHORITY",
    "AdaptiveLeafOverlayError",
    "COVER_FORMULATION",
    "DESCENDANT_FIELDS",
    "HARD_EVIDENCE_FIELDS",
    "HARD_EVIDENCE_KIND",
    "MANIFEST_FIELDS",
    "MANIFEST_KIND",
    "ONE_SPLIT_MAX_DEPTH",
    "ONE_SPLIT_MAX_NODES",
    "PENDING_SOURCE",
    "PENDING_STATUS",
    "PHYSICAL_VARIABLE_MAX",
    "PHYSICAL_VARIABLE_MIN",
    "SCHEMA_VERSION",
    "TIMEOUT_POLICY_FIELDS",
    "VERIFICATION_FIELDS",
    "VERIFICATION_KIND",
    "acquire_campaign_replay_token",
    "build_hard_evidence_record",
    "build_overlay_manifest",
    "canonical_bytes",
    "canonical_sha256",
    "json_type_equal",
    "seal",
    "selfhash_valid",
    "verify_overlay_manifest",
]
