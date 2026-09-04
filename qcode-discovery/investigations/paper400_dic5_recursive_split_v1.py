#!/usr/bin/env python3
"""Audited recursive splitting primitives for the paper400 proof campaign.

This module is deliberately independent of the original v1 runner.  Existing
v1 roots bind the exact bytes of their runner and must not be rewritten in
place.  A split is represented by a *binary* tree, even when the requested
fan-out is four or eight.  Thus every internal node has the complementary
children ``P and x`` and ``P and not x``; the final frontier contains exactly
``fanout`` mutually exclusive and exhaustive formulas.

The module does not decide UNSAT.  A timeout is hardness evidence only.  The
only operation that can derive a parent UNSAT result is
``aggregate_child_certificates`` after every descendant has a complete,
freshly replayed proof certificate.  It also provides a small, persistence-
friendly CPU-time ledger used by the sidecar supervisor: solver CPU counters
advance only while a solver generation is observed RUNNING, never while a
checkpoint, checker, or terminal action is active.
"""

from __future__ import annotations

import contextlib
import fcntl
import hashlib
import json
import math
import os
import re
import secrets
import shutil
import stat
import time
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
MODULE_KIND = "paper400-dic5-recursive-split-v1"
SOLVER_TIMEOUT_SECONDS = 12 * 60 * 60
DEFAULT_FANOUT = 4
SUPPORTED_FANOUTS = (2, 4, 8)
MAX_FANOUT = max(SUPPORTED_FANOUTS)
DEFAULT_MAX_SPLITS_PER_PASS = 1
HASH_CHUNK_BYTES = 8 << 20
MAX_DIMACS_BYTES = 1 << 40
MAX_JSON_BYTES = 256 << 20

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_PATH_RE = re.compile(r"^[01]+$")

# The manifest is intentionally a small, versioned interchange format.  A
# leaf hash is the hash of the complete unsigned leaf record (including the
# exact child-CNF hashes), rather than an alias for the DIMACS hash.  This is
# what lets a certificate bind to one particular frontier item without
# relying on a positional index that can change when a queue is resumed.
MANIFEST_REQUIRED_FIELDS = frozenset({
    "schema_version", "kind", "manifest_kind", "parent", "split_policy",
    "root", "nodes", "leaves", "coverage", "ancestry_sha256", "claim_scope",
    "source", "certificate_binding", "manifest_sha256",
})
MANIFEST_OPTIONAL_FIELDS = frozenset({"trigger"})
NODE_FIELDS = frozenset({
    "node_id", "parent_node_id", "path", "depth", "assumptions",
    "cube_sha256", "selected_variable", "positive_child_id",
    "negative_child_id", "positive_edge_literal", "negative_edge_literal",
    "node_sha256",
})
LEAF_FIELDS = frozenset({
    "leaf_index", "leaf_id", "path", "node_id", "parent_node_id", "depth",
    "assumptions", "cube_sha256", "child_num_variables",
    "child_num_clauses", "child_dimacs_bytes", "child_dimacs_sha256",
    "child_cnf_sha256", "status", "hardness_only", "solver_terminal_claim",
    "leaf_sha256",
})

TRIGGER_FIELDS = frozenset({
    "kind", "reason", "observed_state", "timeout_seconds",
    "effective_solver_seconds", "timed_out", "hardness_only",
    "solver_terminal_claim", "ledger_sha256", "evidence", "evidence_sha256",
    "trigger_sha256",
})

# Version 2 adds the variable/clause count fields that are already mandatory
# in a leaf proof certificate.  Without them a queue item cannot independently
# prove that a certificate belongs to its exact child formula.
QUEUE_SCHEMA_VERSION = 2
QUEUE_KIND = "paper400-dic5-recursive-split-queue-v2"
QUEUE_ITEM_STATES = frozenset({"PENDING", "CLAIMED", "CERTIFIED", "FAILED"})
QUEUE_TERMINAL_STATES = frozenset({"CERTIFIED", "FAILED"})
QUEUE_STATUS_OPEN = "OPEN"
QUEUE_STATUS_COMPLETE = "COMPLETE"
QUEUE_STATUS_FAILED = "FAILED"
QUEUE_LEASE_SECONDS = 6 * 60 * 60
QUEUE_MAX_LEASE_SECONDS = 7 * 24 * 60 * 60
QUEUE_ITEM_FIELDS = frozenset({
    "item_id", "parent_id", "parent_manifest_sha256", "split_manifest_sha256",
    "leaf_id", "leaf_sha256", "path", "depth", "child_cnf_sha256",
    "child_dimacs_sha256", "child_num_variables", "child_num_clauses",
    "child_dimacs_bytes", "cpu_slots", "cpu_ids",
    "state", "claim", "attempts", "last_error", "certificate_sha256",
    "item_sha256",
})

# Cleanup is a two-phase irreversible operation.  The claim is published and
# fsynced before any transport entry is removed; the commit is published only
# after the removal has been fsynced.  Keeping the names fixed also gives a
# crashed sidecar a deterministic recovery point.
CLEANUP_CLAIM_NAME = "parent-transport-cleanup.claim.json"
CLEANUP_COMMIT_NAME = "parent-transport-cleanup.json"
CLEANUP_CLAIM_KIND = "paper400-dic5-parent-transport-cleanup-claim-v1"
CLEANUP_COMMIT_KIND = "paper400-dic5-parent-transport-cleanup-v1"
CLEANUP_MAX_ENTRIES = 2_000_000
QUEUE_CLAIM_FIELDS = frozenset({
    "worker_id", "token", "claimed_at", "lease_expires_at", "cpu_slots",
    "cpu_ids",
})
QUEUE_FIELDS = frozenset({
    "schema_version", "kind", "queue_id", "parent_id",
    "parent_manifest_sha256", "split_manifest_sha256", "ancestry_sha256",
    "fanout", "cpu_pool", "cpu_capacity", "default_cpu_slots",
    "lease_seconds", "created_at", "updated_at", "status", "items",
    "event_sequence", "recovery_count", "queue_sha256",
})


class RecursiveSplitError(RuntimeError):
    """A split, timing, aggregation, or cleanup invariant failed."""


def canonical_bytes(value: Any) -> bytes:
    """Encode strict canonical JSON used by every persisted record."""

    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise RecursiveSplitError(f"value is not canonical JSON: {exc}") from exc


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    if type(value) is not dict or field in value:
        raise RecursiveSplitError("seal requires one plain, unsealed object")
    result = dict(value)
    result[field] = canonical_sha256(result)
    return result


def is_sha256(value: Any) -> bool:
    return type(value) is str and _SHA256_RE.fullmatch(value) is not None


def selfhash_valid(value: Any, field: str = "record_sha256") -> bool:
    if type(value) is not dict or not is_sha256(value.get(field)):
        return False
    unsigned = dict(value)
    expected = unsigned.pop(field)
    try:
        return expected == canonical_sha256(unsigned)
    except RecursiveSplitError:
        return False


def _same(left: Any, right: Any) -> bool:
    """Type-sensitive JSON equality (``True`` must not equal ``1``)."""

    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(
            _same(left[key], right[key]) for key in left
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            _same(a, b) for a, b in zip(left, right, strict=True)
        )
    return left == right


def validate_fanout(fanout: Any) -> int:
    """Validate the supported final frontier sizes.

    Fan-out is intentionally limited to powers of two.  The implementation
    uses ``log2(fanout)`` binary levels, which makes coverage auditable and
    avoids a many-way primitive that could accidentally omit a complement.
    """

    if type(fanout) is not int or fanout not in SUPPORTED_FANOUTS:
        raise RecursiveSplitError(
            f"fanout must be one of {SUPPORTED_FANOUTS}, got {fanout!r}"
        )
    return fanout


def fanout_depth(fanout: Any) -> int:
    value = validate_fanout(fanout)
    return value.bit_length() - 1


def frontier_paths(fanout: Any) -> list[str]:
    depth = fanout_depth(fanout)
    return [format(index, f"0{depth}b") for index in range(validate_fanout(fanout))]


def split_factor_for_cpu(
    available_cpu: Any, *, minimum: int = 2, maximum: int = MAX_FANOUT,
) -> int:
    """Choose a safe power-of-two fan-out from available worker slots.

    This is only a scheduling hint.  It never changes an already-authenticated
    manifest.  The returned value is capped at the supported frontier size and
    is deliberately conservative when fewer than two slots are available.
    """

    if type(available_cpu) is not int or available_cpu < 1:
        raise RecursiveSplitError("available_cpu must be a positive integer")
    if type(minimum) is not int or minimum not in SUPPORTED_FANOUTS:
        raise RecursiveSplitError("minimum fanout is unsupported")
    if type(maximum) is not int or maximum not in SUPPORTED_FANOUTS:
        raise RecursiveSplitError("maximum fanout is unsupported")
    if minimum > maximum:
        raise RecursiveSplitError("minimum fanout exceeds maximum fanout")
    candidates = [value for value in SUPPORTED_FANOUTS if minimum <= value <= maximum]
    eligible = [value for value in candidates if value <= available_cpu]
    # If fewer than ``minimum`` workers are free, retain the requested
    # minimum as a plan (the caller may wait for capacity); this function is a
    # policy selector, not permission to launch with an undersized pool.
    return max(eligible, default=minimum)


def fanout_for_available_cpus(
    available_cpu: Any, *, minimum: int = 2, maximum: int = MAX_FANOUT,
) -> int:
    """Explicitly named alias for scheduler integrations."""

    return split_factor_for_cpu(
        available_cpu, minimum=minimum, maximum=maximum,
    )


def _safe_text(value: Any, *, label: str, maximum: int = 256) -> str:
    if type(value) is not str or not value or len(value) > maximum:
        raise RecursiveSplitError(f"{label} is invalid")
    if "\x00" in value:
        raise RecursiveSplitError(f"{label} contains NUL")
    return value


def _safe_worker_id(value: Any) -> str:
    worker = _safe_text(value, label="worker_id", maximum=128)
    if re.fullmatch(r"[A-Za-z0-9_.:@+-]+", worker) is None:
        raise RecursiveSplitError("worker_id contains unsafe characters")
    return worker


def _finite_timestamp(value: Any, *, label: str) -> float:
    result = _finite_nonnegative(value, label=label)
    # A timestamp far in the past/future usually indicates a unit mistake or
    # a corrupted queue.  Keep the bound generous for test fixtures and clock
    # restoration after a reboot.
    if result > 10**12:
        raise RecursiveSplitError(f"{label} is outside the supported range")
    return result


def _parse_int(token: str, *, label: str) -> int:
    try:
        return int(token, 10)
    except ValueError as exc:
        raise RecursiveSplitError(f"invalid {label}: {token!r}") from exc


def parse_dimacs(payload: bytes | str) -> dict[str, Any]:
    """Parse a bounded DIMACS CNF without invoking a solver."""

    raw = payload.encode("ascii") if isinstance(payload, str) else bytes(payload)
    if len(raw) > MAX_DIMACS_BYTES:
        raise RecursiveSplitError("DIMACS exceeds size cap")
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise RecursiveSplitError("DIMACS is not ASCII") from exc
    variables: int | None = None
    declared_clauses: int | None = None
    clauses: list[list[int]] = []
    pending: list[int] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("c"):
            continue
        if stripped.startswith("p "):
            if variables is not None:
                raise RecursiveSplitError("duplicate DIMACS header")
            fields = stripped.split()
            if len(fields) != 4 or fields[1] != "cnf":
                raise RecursiveSplitError(f"invalid DIMACS header at line {line_number}")
            variables = _parse_int(fields[2], label="variable count")
            declared_clauses = _parse_int(fields[3], label="clause count")
            if variables < 0 or declared_clauses < 0:
                raise RecursiveSplitError("DIMACS counts must be non-negative")
            continue
        for token in stripped.split():
            literal = _parse_int(token, label="literal")
            if literal == 0:
                if not pending:
                    # Empty clauses are represented by a line containing 0.
                    clauses.append([])
                else:
                    clauses.append(list(pending))
                    pending.clear()
            else:
                pending.append(literal)
    if variables is None or declared_clauses is None:
        raise RecursiveSplitError("DIMACS header is missing")
    if pending:
        raise RecursiveSplitError("unterminated DIMACS clause")
    if len(clauses) != declared_clauses:
        raise RecursiveSplitError(
            f"DIMACS clause count mismatch: declared {declared_clauses}, observed {len(clauses)}"
        )
    for clause in clauses:
        seen: set[int] = set()
        for literal in clause:
            if literal == 0 or abs(literal) > variables:
                raise RecursiveSplitError("DIMACS literal is outside the header range")
            if -literal in seen:
                # Tautologies are legal DIMACS.  Keep the input exactly; this
                # parser is a binding/replay layer, not a simplifier.
                pass
            seen.add(literal)
    return {
        "variables": variables,
        "clauses": clauses,
        "declared_clauses": declared_clauses,
        "payload_sha256": hashlib.sha256(raw).hexdigest(),
        "payload_bytes": len(raw),
    }


def render_dimacs(parsed_or_variables: Mapping[str, Any] | int,
                  clauses: Sequence[Sequence[int]] | None = None) -> bytes:
    if isinstance(parsed_or_variables, Mapping):
        variables = parsed_or_variables.get("variables")
        source_clauses = parsed_or_variables.get("clauses")
        if clauses is None:
            clauses = source_clauses
    else:
        variables = parsed_or_variables
    if type(variables) is not int or variables < 0 or clauses is None:
        raise RecursiveSplitError("invalid DIMACS render inputs")
    normalized: list[list[int]] = []
    for clause in clauses or []:
        if not isinstance(clause, (list, tuple)):
            raise RecursiveSplitError("clause is not a sequence")
        row: list[int] = []
        for literal in clause:
            if type(literal) is not int or literal == 0 or abs(literal) > variables:
                raise RecursiveSplitError("render literal is outside DIMACS range")
            row.append(literal)
        normalized.append(row)
    lines = [f"p cnf {variables} {len(normalized)}"]
    lines.extend(" ".join(str(item) for item in clause) + " 0" for clause in normalized)
    return ("\n".join(lines) + "\n").encode("ascii")


def structural_cnf_sha256(variables: int, clauses: Sequence[Sequence[int]]) -> str:
    normalized = [[int(literal) for literal in clause] for clause in clauses]
    return canonical_sha256({
        "num_variables": variables,
        "clauses": normalized,
        "native_atmost": None,
    })


def _normalize_assumptions(assumptions: Sequence[int]) -> list[int]:
    if not isinstance(assumptions, (list, tuple)):
        raise RecursiveSplitError("assumptions must be a list or tuple")
    result: list[int] = []
    seen: dict[int, int] = {}
    for literal in assumptions:
        if type(literal) is not int or literal == 0:
            raise RecursiveSplitError("assumption literal is invalid")
        variable = abs(literal)
        old = seen.get(variable)
        if old is not None:
            if old != literal:
                raise RecursiveSplitError("assumptions contain a contradiction")
            raise RecursiveSplitError("assumptions repeat a variable")
        seen[variable] = literal
        result.append(literal)
    return result


def _assignment(assumptions: Sequence[int]) -> dict[int, int]:
    return {abs(literal): (1 if literal > 0 else 0) for literal in assumptions}


def _candidate_score(
    variable: int, clauses: Sequence[Sequence[int]], assigned: set[int],
) -> tuple[int, int, int, int]:
    positive = 0
    negative = 0
    for clause in clauses:
        for literal in clause:
            if abs(literal) != variable:
                continue
            if literal > 0:
                positive += 1
            else:
                negative += 1
    # Higher two-sided incidence is preferred, then balanced signs, then
    # total incidence.  The final variable number makes the choice stable.
    return (-min(positive, negative), abs(positive - negative),
            -(positive + negative), variable)


def choose_split_variables(
    parent_dimacs: bytes | str,
    parent_assumptions: Sequence[int],
    count: int,
    *,
    candidate_variables: Sequence[int] | None = None,
) -> list[int]:
    """Choose deterministic physical variables for one Cartesian split."""

    parsed = parse_dimacs(parent_dimacs)
    assumptions = _normalize_assumptions(parent_assumptions)
    if type(count) is not int or not 1 <= count <= fanout_depth(MAX_FANOUT):
        raise RecursiveSplitError("split variable count must be in 1..3")
    assigned = set(map(abs, assumptions))
    if candidate_variables is None:
        candidates = list(range(1, parsed["variables"] + 1))
    else:
        candidates = []
        for variable in candidate_variables:
            if type(variable) is not int or not 1 <= variable <= parsed["variables"]:
                raise RecursiveSplitError("candidate variable is outside DIMACS range")
            if variable in candidates:
                raise RecursiveSplitError("candidate variables contain duplicates")
            candidates.append(variable)
    candidates = [variable for variable in candidates if variable not in assigned]
    candidates.sort(key=lambda variable: _candidate_score(variable, parsed["clauses"], assigned))
    if len(candidates) < count:
        raise RecursiveSplitError("not enough unassigned split variables")
    return candidates[:count]


def _child_payload(
    parsed: Mapping[str, Any], assumptions: Sequence[int],
) -> tuple[bytes, str, str]:
    normalized = _normalize_assumptions(assumptions)
    clauses = [list(map(int, clause)) for clause in parsed["clauses"]]
    clauses.extend([[literal] for literal in normalized])
    payload = render_dimacs(parsed["variables"], clauses)
    return payload, structural_cnf_sha256(parsed["variables"], clauses), hashlib.sha256(payload).hexdigest()


def _cube_hash(assumptions: Sequence[int]) -> str:
    return canonical_sha256(list(assumptions))


def _validate_split_variables(
    parsed: Mapping[str, Any], assumptions: Sequence[int], variables: Sequence[int],
    depth: int,
) -> list[int]:
    if type(variables) not in {list, tuple} or len(variables) != depth:
        raise RecursiveSplitError(f"exactly {depth} split variables are required")
    assigned = set(map(abs, _normalize_assumptions(assumptions)))
    result: list[int] = []
    for variable in variables:
        if (
            type(variable) is not int
            or not 1 <= variable <= parsed["variables"]
            or variable in assigned
            or variable in result
        ):
            raise RecursiveSplitError("split variables are invalid or already assigned")
        result.append(variable)
    return result


def build_binary_cover(
    parent_dimacs: bytes | str,
    *,
    parent_assumptions: Sequence[int] = (),
    fanout: int = DEFAULT_FANOUT,
    split_variables: Sequence[int] | None = None,
    candidate_variables: Sequence[int] | None = None,
    parent_id: str = "parent",
    ancestry_sha256: str | None = None,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    """Build a sealed binary tree and its child DIMACS payloads.

    ``fanout=4`` creates two internal levels and four leaves (``00``, ``01``,
    ``10``, ``11``).  The returned payload map is separate from the manifest so
    large CNFs are not duplicated inside JSON evidence.
    """

    fanout = validate_fanout(fanout)
    parsed = parse_dimacs(parent_dimacs)
    assumptions = _normalize_assumptions(parent_assumptions)
    depth = fanout_depth(fanout)
    if split_variables is None:
        variables = choose_split_variables(
            parent_dimacs, assumptions, depth,
            candidate_variables=candidate_variables,
        )
    else:
        variables = _validate_split_variables(parsed, assumptions, split_variables, depth)
    if type(parent_id) is not str or not parent_id or "/" in parent_id:
        raise RecursiveSplitError("parent_id must be a non-empty simple string")
    if ancestry_sha256 is not None and not is_sha256(ancestry_sha256):
        raise RecursiveSplitError("ancestry_sha256 is invalid")

    nodes: list[dict[str, Any]] = []
    leaves: list[dict[str, Any]] = []
    payloads: dict[str, bytes] = {}

    def walk(path: str, current: list[int], level: int, node_id: str,
             parent_node_id: str | None) -> None:
        cube_hash = _cube_hash(current)
        if level == depth:
            payload, cnf_hash, dimacs_hash = _child_payload(parsed, current)
            leaf = seal({
                "leaf_index": len(leaves),
                "leaf_id": f"{parent_id}:{path}",
                "path": path,
                "node_id": node_id,
                "parent_node_id": parent_node_id,
                "depth": level,
                "assumptions": list(current),
                "cube_sha256": cube_hash,
                "child_num_variables": parsed["variables"],
                "child_num_clauses": parsed["declared_clauses"] + len(current),
                "child_dimacs_bytes": len(payload),
                "child_dimacs_sha256": dimacs_hash,
                "child_cnf_sha256": cnf_hash,
                "status": "PENDING",
                "hardness_only": False,
                "solver_terminal_claim": False,
            }, "leaf_sha256")
            leaves.append(leaf)
            payloads[path] = payload
            return
        variable = variables[level]
        positive_id = f"{node_id}0"
        negative_id = f"{node_id}1"
        node = seal({
            "node_id": node_id,
            "parent_node_id": parent_node_id,
            "path": path,
            "depth": level,
            "assumptions": list(current),
            "cube_sha256": cube_hash,
            "selected_variable": variable,
            "positive_child_id": positive_id,
            "negative_child_id": negative_id,
            "positive_edge_literal": variable,
            "negative_edge_literal": -variable,
        }, "node_sha256")
        nodes.append(node)
        walk(path + "0", [*current, variable], level + 1, positive_id, node_id)
        walk(path + "1", [*current, -variable], level + 1, negative_id, node_id)

    walk("", assumptions, 0, "r", None)
    parent_payload = parent_dimacs.encode("ascii") if isinstance(parent_dimacs, str) else bytes(parent_dimacs)
    manifest_unsigned: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "kind": MODULE_KIND,
        "manifest_kind": "paper400-dic5-recursive-binary-cover-v1",
        "parent": {
            "parent_id": parent_id,
            "assumptions": assumptions,
            "cube_sha256": _cube_hash(assumptions),
            "dimacs_sha256": hashlib.sha256(parent_payload).hexdigest(),
            "dimacs_bytes": len(parent_payload),
            "num_variables": parsed["variables"],
            "num_clauses": parsed["declared_clauses"],
        },
        "split_policy": {
            "fanout": fanout,
            "binary_depth": depth,
            "split_variables": variables,
            "selection_method": "two-sided-occurrence-balanced-v1",
            "recursive": True,
        },
        "root": {
            "node_id": "r",
            "path": "",
            "depth": 0,
            "assumptions": assumptions,
        },
        "nodes": nodes,
        "leaves": leaves,
        "coverage": {
            "expected_leaf_count": fanout,
            "observed_leaf_count": len(leaves),
            "frontier_paths": [leaf["path"] for leaf in leaves],
            "mutually_exclusive": True,
            "exhaustive": True,
            "formula_equivalence": "P <=> OR_a(P AND binary_path_assignment_a)",
            "proof_method": "complementary-binary-tree-replay-v1",
        },
        "certificate_binding": {
            "method": "exact-frontier-leaf-record-sha256-v1",
            "leaf_identity_fields": ["leaf_id", "leaf_sha256"],
            "leaf_sha256_sequence_sha256": canonical_sha256([
                leaf["leaf_sha256"] for leaf in leaves
            ]),
            "expected_certificate_count": fanout,
            "certificate_must_bind_child_cnf": True,
            "timeout_is_not_certificate": True,
        },
        "ancestry_sha256": ancestry_sha256,
        "claim_scope": {
            "timeout_is_hardness_only": True,
            "cover_alone_proves_unsat": False,
            "all_descendant_proofs_required": True,
            "global_distance_claim": False,
        },
        "source": {
            "module": MODULE_KIND,
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        },
    }
    manifest = seal(manifest_unsigned, "manifest_sha256")
    verify_cover(manifest, parent_payload)
    return manifest, payloads


def _leaf_by_path(manifest: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    leaves = manifest.get("leaves")
    if type(leaves) is not list:
        raise RecursiveSplitError("manifest leaves are missing")
    result: dict[str, dict[str, Any]] = {}
    for leaf in leaves:
        if type(leaf) is not dict or type(leaf.get("path")) is not str:
            raise RecursiveSplitError("manifest leaf is malformed")
        if set(leaf) != LEAF_FIELDS or not selfhash_valid(leaf, "leaf_sha256"):
            raise RecursiveSplitError("manifest leaf schema/self-hash mismatch")
        if leaf["path"] in result:
            raise RecursiveSplitError("manifest has duplicate leaf paths")
        result[leaf["path"]] = leaf
    return result


def verify_cover(manifest: Mapping[str, Any], parent_dimacs: bytes | str) -> dict[str, Any]:
    """Replay all tree and formula bindings; raise on any mismatch."""

    if type(manifest) is not dict or not selfhash_valid(manifest, "manifest_sha256"):
        raise RecursiveSplitError("manifest self-hash is invalid")
    if (
        not MANIFEST_REQUIRED_FIELDS.issubset(manifest)
        or set(manifest) - (MANIFEST_REQUIRED_FIELDS | MANIFEST_OPTIONAL_FIELDS)
    ):
        raise RecursiveSplitError("manifest field set mismatch")
    if manifest.get("schema_version") != SCHEMA_VERSION or manifest.get("kind") != MODULE_KIND:
        raise RecursiveSplitError("manifest schema/kind mismatch")
    trigger = manifest.get("trigger")
    if trigger is not None:
        _normalize_trigger(trigger)
    policy = manifest.get("split_policy")
    if type(policy) is not dict:
        raise RecursiveSplitError("split policy is missing")
    fanout = validate_fanout(policy.get("fanout"))
    depth = fanout_depth(fanout)
    if policy.get("binary_depth") != depth or type(policy.get("split_variables")) is not list:
        raise RecursiveSplitError("split policy depth/variables mismatch")
    parsed = parse_dimacs(parent_dimacs)
    parent = manifest.get("parent")
    if type(parent) is not dict:
        raise RecursiveSplitError("parent binding is missing")
    parent_assumptions = _normalize_assumptions(parent.get("assumptions", []))
    parent_payload = parent_dimacs.encode("ascii") if isinstance(parent_dimacs, str) else bytes(parent_dimacs)
    if (
        parent.get("dimacs_sha256") != hashlib.sha256(parent_payload).hexdigest()
        or parent.get("dimacs_bytes") != len(parent_payload)
        or parent.get("num_variables") != parsed["variables"]
        or parent.get("num_clauses") != parsed["declared_clauses"]
        or parent.get("cube_sha256") != _cube_hash(parent_assumptions)
    ):
        raise RecursiveSplitError("parent binding mismatch")
    variables = _validate_split_variables(
        parsed, parent_assumptions, policy["split_variables"], depth,
    )
    nodes = manifest.get("nodes")
    leaves = manifest.get("leaves")
    if type(nodes) is not list or type(leaves) is not list:
        raise RecursiveSplitError("manifest tree arrays are missing")
    expected_paths = frontier_paths(fanout)
    if len(leaves) != fanout or [leaf.get("path") for leaf in leaves] != expected_paths:
        raise RecursiveSplitError("manifest frontier cardinality/order mismatch")
    node_by_id: dict[str, dict[str, Any]] = {}
    for node in nodes:
        if type(node) is not dict or type(node.get("node_id")) is not str:
            raise RecursiveSplitError("manifest node is malformed")
        if set(node) != NODE_FIELDS or not selfhash_valid(node, "node_sha256"):
            raise RecursiveSplitError("manifest node schema/self-hash mismatch")
        if node["node_id"] in node_by_id:
            raise RecursiveSplitError("manifest node IDs are not unique")
        node_by_id[node["node_id"]] = node
    leaf_map = _leaf_by_path(manifest)
    if set(leaf_map) != set(expected_paths):
        raise RecursiveSplitError("manifest paths are incomplete")

    # Replay the exact expected full tree from the root.  This catches aliased
    # children, skipped levels, and a changed variable at one branch.
    visited_nodes: set[str] = set()
    visited_leaves: set[str] = set()

    def walk(node_id: str, path: str, current: list[int], level: int,
             parent_id: str | None) -> None:
        if level == depth:
            leaf = leaf_map.get(path)
            if leaf is None:
                raise RecursiveSplitError("tree references a missing leaf")
            if leaf.get("node_id") != node_id or leaf.get("parent_node_id") != parent_id:
                raise RecursiveSplitError("leaf parent/node binding mismatch")
            if leaf.get("depth") != level or leaf.get("assumptions") != current:
                raise RecursiveSplitError("leaf assumptions/depth mismatch")
            payload, cnf_hash, dimacs_hash = _child_payload(parsed, current)
            if (
                leaf.get("leaf_index") != expected_paths.index(path)
                or leaf.get("leaf_id") != f"{manifest['parent']['parent_id']}:{path}"
                or leaf.get("cube_sha256") != _cube_hash(current)
                or leaf.get("child_num_variables") != parsed["variables"]
                or leaf.get("child_num_clauses") != parsed["declared_clauses"] + len(current)
                or leaf.get("child_dimacs_bytes") != len(payload)
                or leaf.get("child_dimacs_sha256") != dimacs_hash
                or leaf.get("child_cnf_sha256") != cnf_hash
            ):
                raise RecursiveSplitError("leaf formula binding mismatch")
            visited_leaves.add(path)
            return
        node = node_by_id.get(node_id)
        if node is None or node_id in visited_nodes:
            raise RecursiveSplitError("node is missing or shared by two branches")
        visited_nodes.add(node_id)
        if (
            node.get("path") != path
            or node.get("depth") != level
            or node.get("parent_node_id") != parent_id
            or node.get("assumptions") != current
            or node.get("cube_sha256") != _cube_hash(current)
            or node.get("selected_variable") != variables[level]
            or node.get("positive_edge_literal") != variables[level]
            or node.get("negative_edge_literal") != -variables[level]
        ):
            raise RecursiveSplitError("internal node binding mismatch")
        positive = node.get("positive_child_id")
        negative = node.get("negative_child_id")
        if type(positive) is not str or type(negative) is not str or positive == negative:
            raise RecursiveSplitError("internal node children are malformed")
        walk(positive, path + "0", [*current, variables[level]], level + 1, node_id)
        walk(negative, path + "1", [*current, -variables[level]], level + 1, node_id)

    walk("r", "", list(parent_assumptions), 0, None)
    if visited_leaves != set(expected_paths) or len(visited_nodes) != len(nodes):
        raise RecursiveSplitError("tree contains unreachable nodes or leaves")
    coverage = manifest.get("coverage")
    if (
        type(coverage) is not dict
        or coverage.get("expected_leaf_count") != fanout
        or coverage.get("observed_leaf_count") != fanout
        or coverage.get("frontier_paths") != expected_paths
        or coverage.get("mutually_exclusive") is not True
        or coverage.get("exhaustive") is not True
    ):
        raise RecursiveSplitError("coverage record is not authenticated")
    # Pairwise incompatibility follows from the first differing binary edge;
    # replay it explicitly so a future representation change cannot weaken
    # this invariant.
    for left_index, left_path in enumerate(expected_paths):
        left = leaf_map[left_path]["assumptions"]
        for right_path in expected_paths[left_index + 1:]:
            right = leaf_map[right_path]["assumptions"]
            if not any(a == -b for a in left for b in right):
                raise RecursiveSplitError("frontier leaves are not exclusive")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-recursive-cover-verification-v1",
        "manifest_sha256": manifest["manifest_sha256"],
        "fanout": fanout,
        "binary_depth": depth,
        "leaf_count": len(leaves),
        "mutually_exclusive": True,
        "exhaustive": True,
        "valid": True,
        "scientific_claim": False,
    }, "record_sha256")


def render_leaf_payload(manifest: Mapping[str, Any], parent_dimacs: bytes | str,
                       path: str) -> bytes:
    """Render one verified descendant only after replaying the whole cover."""

    verify_cover(manifest, parent_dimacs)
    leaves = _leaf_by_path(manifest)
    leaf = leaves.get(path)
    if leaf is None:
        raise RecursiveSplitError("unknown descendant path")
    parsed = parse_dimacs(parent_dimacs)
    payload, cnf_hash, dimacs_hash = _child_payload(parsed, leaf["assumptions"])
    if leaf["child_dimacs_sha256"] != dimacs_hash or leaf["child_cnf_sha256"] != cnf_hash:
        raise RecursiveSplitError("descendant payload hash mismatch")
    return payload


def build_split_manifest(
    parent_dimacs: bytes | str,
    *,
    parent_id: str,
    parent_assumptions: Sequence[int] = (),
    fanout: int = DEFAULT_FANOUT,
    split_variables: Sequence[int] | None = None,
    candidate_variables: Sequence[int] | None = None,
    trigger: Mapping[str, Any] | None = None,
    ancestry_sha256: str | None = None,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    """Public spelling used by supervisors and material builders."""

    manifest, payloads = build_binary_cover(
        parent_dimacs,
        parent_assumptions=parent_assumptions,
        fanout=fanout,
        split_variables=split_variables,
        candidate_variables=candidate_variables,
        parent_id=parent_id,
        ancestry_sha256=ancestry_sha256,
    )
    if trigger is not None:
        if type(trigger) is not dict:
            raise RecursiveSplitError("split trigger must be a plain object")
        trigger = _normalize_trigger(trigger)
        # Re-seal after adding the immutable hardness observation.  It is
        # intentionally not interpreted as a solver terminal result.
        updated = dict(manifest)
        updated.pop("manifest_sha256", None)
        updated["trigger"] = dict(trigger)
        updated["claim_scope"] = {
            **dict(updated["claim_scope"]),
            "trigger_is_hardness_evidence_only": True,
        }
        manifest = seal(updated, "manifest_sha256")
        verify_cover(manifest, parent_dimacs)
    return manifest, payloads


# ---------------------------------------------------------------------------
# Effective solver-time accounting


def _finite_nonnegative(value: Any, *, label: str) -> float:
    if type(value) not in {int, float} or isinstance(value, bool):
        raise RecursiveSplitError(f"{label} is not numeric")
    result = float(value)
    if not math.isfinite(result) or result < 0:
        raise RecursiveSplitError(f"{label} is not finite/non-negative")
    return result


def new_timing_ledger(leaf_id: str, *, timeout_seconds: float = SOLVER_TIMEOUT_SECONDS) -> dict[str, Any]:
    if type(leaf_id) is not str or not leaf_id:
        raise RecursiveSplitError("leaf_id must be a non-empty string")
    timeout = _finite_nonnegative(timeout_seconds, label="timeout_seconds")
    if timeout <= 0:
        raise RecursiveSplitError("timeout_seconds must be positive")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-effective-solver-time-ledger-v1",
        "leaf_id": leaf_id,
        "timeout_seconds": timeout,
        "effective_solver_seconds": 0.0,
        "last_generation": None,
        "last_pid": None,
        "last_proc_start_ticks": None,
        "last_cpu_seconds": None,
        "last_observed_monotonic": None,
        "sample_count": 0,
        "state": "UNOBSERVED",
        "timing_policy": {
            "clock": "solver-process-cpu-time",
            "running_state_only": True,
            "checkpoint_time_included": False,
            "checker_time_included": False,
            "terminal_time_included": False,
        },
        "hardness_only": True,
        "solver_terminal_claim": False,
    }, "ledger_sha256")


def _ledger_unsigned(ledger: Mapping[str, Any]) -> dict[str, Any]:
    if type(ledger) is not dict or not selfhash_valid(ledger, "ledger_sha256"):
        raise RecursiveSplitError("timing ledger self-hash is invalid")
    result = dict(ledger)
    result.pop("ledger_sha256")
    return result


def update_timing_ledger(
    ledger: Mapping[str, Any], sample: Mapping[str, Any],
) -> dict[str, Any]:
    """Add one process sample, counting only a stable RUNNING generation.

    A generation change starts a fresh CPU counter.  A sample in any other
    state merely updates identity/state and contributes zero seconds.  This
    makes checkpoint and checker intervals naturally disappear from the
    cumulative total.
    """

    value = _ledger_unsigned(ledger)
    if type(sample) is not dict:
        raise RecursiveSplitError("timing sample must be a plain object")
    state = sample.get("state")
    if state not in {"RUNNING", "CHECKPOINTED", "INACTIVE", "CHECKER", "FINAL", "SPLIT_PENDING"}:
        raise RecursiveSplitError("unsupported timing sample state")
    generation = sample.get("generation")
    pid = sample.get("pid")
    ticks = sample.get("proc_start_ticks")
    cpu_seconds = sample.get("cpu_seconds")
    observed = sample.get("observed_monotonic", time.monotonic())
    if generation is not None and (type(generation) is not int or generation < 0):
        raise RecursiveSplitError("sample generation is invalid")
    if pid is not None and (type(pid) is not int or pid <= 0):
        raise RecursiveSplitError("sample pid is invalid")
    if ticks is not None and (type(ticks) is not int or ticks < 0):
        raise RecursiveSplitError("sample process start ticks are invalid")
    if cpu_seconds is not None:
        cpu_seconds = _finite_nonnegative(cpu_seconds, label="cpu_seconds")
    observed = _finite_nonnegative(observed, label="observed_monotonic")

    previous_state = value.get("state")
    previous_generation = value.get("last_generation")
    previous_pid = value.get("last_pid")
    previous_ticks = value.get("last_proc_start_ticks")
    previous_cpu = value.get("last_cpu_seconds")
    increment = 0.0
    same_process = (
        generation is not None and generation == previous_generation
        and pid is not None and pid == previous_pid
        and ticks is not None and ticks == previous_ticks
    )
    if state == "RUNNING" and cpu_seconds is not None:
        if same_process and previous_cpu is not None:
            delta = cpu_seconds - float(previous_cpu)
            # Counter resets or a process identity race are not evidence of
            # negative work; restart the baseline at the new observation.
            if delta >= 0 and math.isfinite(delta):
                increment = delta
        elif previous_state not in {"RUNNING", None}:
            # A resumed generation has its own counter.  Count from zero only
            # when the caller explicitly marks the first sample as a fresh
            # baseline; otherwise avoid inventing time at a handoff boundary.
            if sample.get("baseline") is True:
                increment = cpu_seconds
        elif previous_cpu is None or not same_process:
            if sample.get("baseline") is True:
                increment = cpu_seconds
    value["effective_solver_seconds"] = round(
        float(value.get("effective_solver_seconds", 0.0)) + increment, 9,
    )
    # A non-running observation is a hard accounting boundary.  Do not carry
    # its counter into the next running interval: checkpoint/checker/terminal
    # work must never be charged to solver CPU time.
    value["last_generation"] = generation
    value["last_pid"] = pid
    value["last_proc_start_ticks"] = ticks
    value["last_cpu_seconds"] = cpu_seconds if state == "RUNNING" else None
    value["last_observed_monotonic"] = observed
    previous_count = value.get("sample_count", 0)
    if type(previous_count) is not int or previous_count < 0:
        raise RecursiveSplitError("timing ledger sample_count is invalid")
    value["sample_count"] = previous_count + 1
    value["state"] = state
    value["last_increment_seconds"] = round(increment, 9)
    value["hardness_only"] = True
    value["solver_terminal_claim"] = False
    return seal(value, "ledger_sha256")


def effective_solver_seconds(ledger: Mapping[str, Any]) -> float:
    value = _ledger_unsigned(ledger)
    return _finite_nonnegative(value.get("effective_solver_seconds"), label="effective_solver_seconds")


def observe_proc_cpu_seconds(pid: int, *, clock_ticks_per_second: int | None = None) -> dict[str, Any]:
    """Read a solver's ``/proc/<pid>/stat`` CPU counter safely.

    The returned counter is process CPU time (user+system), not wall time.
    ``proc_start_ticks`` is included so a PID reuse cannot be mistaken for a
    continuation.  The parser handles command names containing ``)`` by using
    the final closing parenthesis, as required by the Linux stat format.
    """

    if type(pid) is not int or pid <= 0:
        raise RecursiveSplitError("pid must be a positive integer")
    hz = os.sysconf("SC_CLK_TCK") if clock_ticks_per_second is None else clock_ticks_per_second
    if type(hz) is not int or hz <= 0:
        raise RecursiveSplitError("clock tick rate is invalid")
    try:
        payload = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
    except (OSError, UnicodeDecodeError) as exc:
        raise RecursiveSplitError("cannot read solver process stat") from exc
    close = payload.rfind(")")
    if close <= 0:
        raise RecursiveSplitError("solver process stat is malformed")
    fields = payload[close + 2 :].split()
    # After the command name, fields[0] is Linux field 3 (state); field 14/15
    # are offsets 11/12 and field 22 is offset 19 in this zero-based slice.
    if len(fields) <= 19:
        raise RecursiveSplitError("solver process stat is truncated")
    state = fields[0]
    try:
        utime = int(fields[11])
        stime = int(fields[12])
        start_ticks = int(fields[19])
    except ValueError as exc:
        raise RecursiveSplitError("solver process stat has invalid counters") from exc
    if min(utime, stime, start_ticks) < 0:
        raise RecursiveSplitError("solver process stat has negative counters")
    return {
        "pid": pid,
        "proc_start_ticks": start_ticks,
        "state": state,
        "cpu_ticks": utime + stime,
        "cpu_seconds": (utime + stime) / float(hz),
        "clock_ticks_per_second": hz,
    }


def timeout_reached(ledger: Mapping[str, Any], *, timeout_seconds: float | None = None) -> bool:
    threshold = (
        _finite_nonnegative(timeout_seconds, label="timeout_seconds")
        if timeout_seconds is not None
        else _finite_nonnegative(ledger.get("timeout_seconds"), label="timeout_seconds")
    )
    if threshold <= 0:
        raise RecursiveSplitError("timeout threshold must be positive")
    return effective_solver_seconds(ledger) >= threshold


def build_timeout_evidence(
    ledger: Mapping[str, Any], *, observed_state: str,
) -> dict[str, Any]:
    if observed_state not in {"RUNNING", "CHECKPOINTED", "INACTIVE"}:
        raise RecursiveSplitError("timeout evidence state is invalid")
    seconds = effective_solver_seconds(ledger)
    threshold = _finite_nonnegative(ledger.get("timeout_seconds"), label="timeout_seconds")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-hardness-timeout-evidence-v1",
        "leaf_id": ledger.get("leaf_id"),
        "observed_state": observed_state,
        "effective_solver_seconds": seconds,
        "timeout_seconds": threshold,
        "timed_out": seconds >= threshold,
        "hardness_only": True,
        "solver_terminal_claim": False,
        "unsat_claim": False,
        "measurement_method": "stable-generation-proc-cpu-counter-v1",
        "ledger_sha256": ledger.get("ledger_sha256"),
    }, "evidence_sha256")


def _normalize_trigger(trigger: Mapping[str, Any]) -> dict[str, Any]:
    """Validate and copy an immutable hardness trigger.

    Callers may provide either the compact trigger emitted by
    :func:`split_plan` or a trigger carrying the full timeout evidence.  In
    both cases the evidence digest and the trigger digest are checked before
    it can enter a manifest.
    """

    value = dict(trigger)
    if "trigger_sha256" in value:
        if not selfhash_valid(value, "trigger_sha256"):
            raise RecursiveSplitError("split trigger self-hash is invalid")
    else:
        value = seal(value, "trigger_sha256")
    required = {
        "kind", "reason", "observed_state", "timeout_seconds",
        "effective_solver_seconds", "timed_out", "hardness_only",
        "solver_terminal_claim", "evidence_sha256", "trigger_sha256",
    }
    if set(value) - (required | {"ledger_sha256", "evidence"}) or not required.issubset(value):
        raise RecursiveSplitError("split trigger field set mismatch")
    if (
        value["kind"] != "paper400-dic5-recursive-split-trigger-v1"
        or value["reason"] != "EFFECTIVE_SOLVER_CPU_TIMEOUT"
        or value["observed_state"] not in {"RUNNING", "CHECKPOINTED", "INACTIVE"}
        or value["timed_out"] is not True
        or value["hardness_only"] is not True
        or value["solver_terminal_claim"] is not False
        or not is_sha256(value["evidence_sha256"])
    ):
        raise RecursiveSplitError("split trigger is not hardness-only evidence")
    _finite_nonnegative(value["timeout_seconds"], label="trigger timeout_seconds")
    _finite_nonnegative(value["effective_solver_seconds"], label="trigger effective_solver_seconds")
    if value["effective_solver_seconds"] < value["timeout_seconds"]:
        raise RecursiveSplitError("split trigger is below timeout threshold")
    evidence = value.get("evidence")
    if evidence is not None:
        if type(evidence) is not dict or not selfhash_valid(evidence, "evidence_sha256"):
            raise RecursiveSplitError("embedded timeout evidence is invalid")
        if evidence["evidence_sha256"] != value["evidence_sha256"]:
            raise RecursiveSplitError("trigger/evidence digest mismatch")
    return value


def _validate_certificate_payload(
    certificate: Mapping[str, Any], leaf: Mapping[str, Any],
) -> bool:
    """Check the immutable fields a child certificate must carry.

    This helper is intentionally conservative and schema-agnostic: the
    versioned v4 Paper400 validator performs the full DRAT/LRAT replay checks,
    while this layer verifies that a certificate cannot be attached to the
    wrong frontier formula.
    """

    if type(certificate) is not dict:
        return False
    leaf_id, leaf_hash = _certificate_leaf_binding(certificate)
    if leaf_id != leaf.get("leaf_id") or leaf_hash != leaf.get("leaf_sha256"):
        return False
    # These bindings are mandatory for a production queue.  A certificate
    # that omits them would otherwise be accepted by the optional-field logic
    # and could be attached to the wrong formula.
    for cert_key, leaf_key in (
        ("child_cnf_sha256", "child_cnf_sha256"),
        ("child_dimacs_sha256", "child_dimacs_sha256"),
        ("child_num_variables", "child_num_variables"),
        ("child_num_clauses", "child_num_clauses"),
        ("child_dimacs_bytes", "child_dimacs_bytes"),
    ):
        if cert_key not in certificate or certificate.get(cert_key) != leaf.get(leaf_key):
            return False
    return True


def should_split_for_timeout(
    ledger: Mapping[str, Any], *, observed_state: str,
) -> bool:
    """Return whether a live/stopped leaf is eligible for recursive splitting.

    This is deliberately a narrow scheduling predicate.  It requires an
    authenticated timing ledger, the 12-hour (or explicitly configured)
    effective solver-CPU threshold, and a non-terminal observation.  It never
    interprets a timeout as SAT/UNSAT and never authorizes deletion or launch.
    """

    if observed_state not in {"RUNNING", "CHECKPOINTED", "INACTIVE"}:
        raise RecursiveSplitError("split observation state is invalid")
    return timeout_reached(ledger)


def split_plan(
    parent_dimacs: bytes | str,
    *,
    parent_id: str,
    parent_assumptions: Sequence[int] = (),
    fanout: int = DEFAULT_FANOUT,
    split_variables: Sequence[int] | None = None,
    candidate_variables: Sequence[int] | None = None,
    ledger: Mapping[str, Any] | None = None,
    observed_state: str | None = None,
    ancestry_sha256: str | None = None,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    """Build a split only after an optional, authenticated timeout gate.

    ``ledger`` is optional for offline material generation.  When supplied,
    both the state and the effective CPU-time threshold are recorded in the
    trigger, and an under-threshold ledger is rejected.  The returned manifest
    remains a structural cover; launch and proof authority stay with the
    production runner/checker.
    """

    trigger: dict[str, Any] | None = None
    if ledger is not None:
        if observed_state is None:
            raise RecursiveSplitError("observed_state is required with a ledger")
        if not should_split_for_timeout(ledger, observed_state=observed_state):
            raise RecursiveSplitError("split timeout threshold has not been reached")
        evidence = build_timeout_evidence(ledger, observed_state=observed_state)
        evidence = dict(evidence)
        trigger = seal({
            "kind": "paper400-dic5-recursive-split-trigger-v1",
            "reason": "EFFECTIVE_SOLVER_CPU_TIMEOUT",
            "observed_state": observed_state,
            "timeout_seconds": evidence["timeout_seconds"],
            "effective_solver_seconds": evidence["effective_solver_seconds"],
            "timed_out": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "ledger_sha256": ledger["ledger_sha256"],
            "evidence": evidence,
            "evidence_sha256": evidence["evidence_sha256"],
        }, "trigger_sha256")
    return build_split_manifest(
        parent_dimacs,
        parent_id=parent_id,
        parent_assumptions=parent_assumptions,
        fanout=fanout,
        split_variables=split_variables,
        candidate_variables=candidate_variables,
        trigger=trigger,
        ancestry_sha256=ancestry_sha256,
    )


# ---------------------------------------------------------------------------
# Durable child queue


def _queue_path(path: Path | str) -> Path:
    """Resolve a queue path without following an existing symlink."""

    target = Path(path)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise RecursiveSplitError("queue path must be a normalized absolute path")
    parent = target.parent
    try:
        parent_stat = parent.lstat()
    except OSError as exc:
        raise RecursiveSplitError("queue parent directory is unavailable") from exc
    if (
        stat.S_ISLNK(parent_stat.st_mode)
        or not stat.S_ISDIR(parent_stat.st_mode)
        or parent.resolve(strict=True) != parent
        or parent_stat.st_uid != os.geteuid()
    ):
        raise RecursiveSplitError("queue parent directory is unsafe")
    if target.exists() and target.is_symlink():
        raise RecursiveSplitError("queue file must not be a symlink")
    return target


def _ensure_queue_lock(path: Path) -> Path:
    lock = path.with_name(path.name + ".lock")
    flags = os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(lock, flags, 0o600)
    except OSError as exc:
        raise RecursiveSplitError("cannot create queue lock") from exc
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or stat.S_IMODE(info.st_mode) != 0o600
            or info.st_nlink != 1
        ):
            raise RecursiveSplitError("queue lock has unsafe metadata")
    finally:
        os.close(fd)
    return lock


def _queue_item_unsigned(item: Mapping[str, Any]) -> dict[str, Any]:
    if type(item) is not dict or not selfhash_valid(item, "item_sha256"):
        raise RecursiveSplitError("queue item self-hash is invalid")
    result = dict(item)
    result.pop("item_sha256")
    return result


def _queue_unsigned(queue: Mapping[str, Any]) -> dict[str, Any]:
    if type(queue) is not dict or not selfhash_valid(queue, "queue_sha256"):
        raise RecursiveSplitError("queue self-hash is invalid")
    result = dict(queue)
    result.pop("queue_sha256")
    return result


def _queue_status_from_items(items: Sequence[Mapping[str, Any]]) -> str:
    states = [item.get("state") for item in items]
    if states and all(state == "CERTIFIED" for state in states):
        return QUEUE_STATUS_COMPLETE
    if any(state == "FAILED" for state in states):
        return QUEUE_STATUS_FAILED
    return QUEUE_STATUS_OPEN


def _validate_queue(queue: Mapping[str, Any]) -> dict[str, Any]:
    """Validate a complete queue, including CPU lease disjointness."""

    if set(queue) != QUEUE_FIELDS:
        raise RecursiveSplitError("queue field set mismatch")
    value = _queue_unsigned(queue)
    if value.get("schema_version") != QUEUE_SCHEMA_VERSION or value.get("kind") != QUEUE_KIND:
        raise RecursiveSplitError("queue schema/kind mismatch")
    _safe_text(value.get("queue_id"), label="queue_id", maximum=192)
    _safe_text(value.get("parent_id"), label="parent_id", maximum=192)
    for key in ("parent_manifest_sha256", "ancestry_sha256"):
        if value.get(key) is not None and not is_sha256(value.get(key)):
            raise RecursiveSplitError(f"queue {key} is invalid")
    if not is_sha256(value.get("split_manifest_sha256")):
        raise RecursiveSplitError("queue split manifest hash is invalid")
    fanout = validate_fanout(value.get("fanout"))
    pool = value.get("cpu_pool")
    if type(pool) is not list or any(
        type(cpu) is not int or isinstance(cpu, bool) or cpu < 0 for cpu in pool
    ):
        raise RecursiveSplitError("queue CPU pool is invalid")
    if pool != sorted(set(pool)):
        raise RecursiveSplitError("queue CPU pool must be sorted and unique")
    if value.get("cpu_capacity") != len(pool) or len(pool) < 1:
        raise RecursiveSplitError("queue CPU capacity mismatch")
    slots = value.get("default_cpu_slots")
    if type(slots) is not int or isinstance(slots, bool) or not 1 <= slots <= len(pool):
        raise RecursiveSplitError("queue default CPU slots are invalid")
    lease_seconds = value.get("lease_seconds")
    if type(lease_seconds) not in {int, float} or isinstance(lease_seconds, bool):
        raise RecursiveSplitError("queue lease seconds are invalid")
    lease_seconds = float(lease_seconds)
    if not math.isfinite(lease_seconds) or not 0 < lease_seconds <= QUEUE_MAX_LEASE_SECONDS:
        raise RecursiveSplitError("queue lease seconds are outside bounds")
    for key in ("created_at", "updated_at"):
        _finite_timestamp(value.get(key), label=f"queue {key}")
    if type(value.get("event_sequence")) is not int or isinstance(value.get("event_sequence"), bool) or value["event_sequence"] < 0:
        raise RecursiveSplitError("queue event sequence is invalid")
    if type(value.get("recovery_count")) is not int or isinstance(value.get("recovery_count"), bool) or value["recovery_count"] < 0:
        raise RecursiveSplitError("queue recovery count is invalid")
    items = value.get("items")
    if type(items) is not list or len(items) != fanout:
        raise RecursiveSplitError("queue item count does not match fanout")
    expected_paths = frontier_paths(fanout)
    seen_ids: set[str] = set()
    seen_cpus: set[int] = set()
    claimed_slots = 0
    for position, item in enumerate(items):
        if set(item) != QUEUE_ITEM_FIELDS:
            raise RecursiveSplitError("queue item field set mismatch")
        _queue_item_unsigned(item)
        _safe_text(item.get("item_id"), label="queue item_id", maximum=256)
        if item["item_id"] in seen_ids:
            raise RecursiveSplitError("queue item IDs are duplicated")
        seen_ids.add(item["item_id"])
        if item.get("split_manifest_sha256") != value["split_manifest_sha256"]:
            raise RecursiveSplitError("queue item/manifest binding mismatch")
        if item.get("path") != expected_paths[position] or type(item.get("path")) is not str:
            raise RecursiveSplitError("queue item path/order mismatch")
        if (
            type(item.get("depth")) is not int
            or isinstance(item.get("depth"), bool)
            or item["depth"] != fanout_depth(fanout)
        ):
            raise RecursiveSplitError("queue item depth mismatch")
        for key in ("leaf_sha256", "child_cnf_sha256", "child_dimacs_sha256"):
            if not is_sha256(item.get(key)):
                raise RecursiveSplitError(f"queue item {key} is invalid")
        for key in ("child_num_variables", "child_num_clauses", "child_dimacs_bytes"):
            if type(item.get(key)) is not int or item[key] < 0:
                raise RecursiveSplitError(f"queue item {key} is invalid")
        item_slots = item.get("cpu_slots")
        if type(item_slots) is not int or isinstance(item_slots, bool) or not 1 <= item_slots <= len(pool):
            raise RecursiveSplitError("queue item CPU slots are invalid")
        state = item.get("state")
        if state not in QUEUE_ITEM_STATES:
            raise RecursiveSplitError("queue item state is invalid")
        attempts = item.get("attempts")
        if type(attempts) is not int or isinstance(attempts, bool) or attempts < 0:
            raise RecursiveSplitError("queue item attempts are invalid")
        last_error = item.get("last_error")
        if last_error is not None:
            _safe_text(last_error, label="queue item last_error", maximum=2048)
        cert_hash = item.get("certificate_sha256")
        if cert_hash is not None and not is_sha256(cert_hash):
            raise RecursiveSplitError("queue item certificate hash is invalid")
        cpu_ids = item.get("cpu_ids")
        if type(cpu_ids) is not list or any(type(cpu) is not int or cpu not in pool for cpu in cpu_ids):
            raise RecursiveSplitError("queue item CPU IDs are invalid")
        if cpu_ids != sorted(set(cpu_ids)):
            raise RecursiveSplitError("queue item CPU IDs must be sorted and unique")
        claim = item.get("claim")
        if state == "CLAIMED":
            if type(claim) is not dict or set(claim) != QUEUE_CLAIM_FIELDS:
                raise RecursiveSplitError("claimed queue item has no valid claim")
            _safe_worker_id(claim.get("worker_id"))
            token = claim.get("token")
            if type(token) is not str or re.fullmatch(r"[0-9a-f]{64}", token) is None:
                raise RecursiveSplitError("queue claim token is invalid")
            claimed_at = _finite_timestamp(claim.get("claimed_at"), label="claim claimed_at")
            expires = _finite_timestamp(claim.get("lease_expires_at"), label="claim lease_expires_at")
            if expires <= claimed_at or expires > claimed_at + QUEUE_MAX_LEASE_SECONDS:
                raise RecursiveSplitError("queue claim lease interval is invalid")
            if claim.get("cpu_slots") != item_slots or claim.get("cpu_ids") != cpu_ids:
                raise RecursiveSplitError("queue claim/CPU binding mismatch")
            if len(cpu_ids) != item_slots:
                raise RecursiveSplitError("claimed CPU count does not match slots")
            if seen_cpus.intersection(cpu_ids):
                raise RecursiveSplitError("claimed CPU leases overlap")
            seen_cpus.update(cpu_ids)
            claimed_slots += item_slots
        else:
            if claim is not None or cpu_ids:
                raise RecursiveSplitError("unclaimed queue item retains a CPU lease")
            if state == "CERTIFIED" and cert_hash is None:
                raise RecursiveSplitError("certified queue item has no certificate")
    expected_status = _queue_status_from_items(items)
    if value.get("status") != expected_status:
        raise RecursiveSplitError("queue status is not derived from item states")
    if claimed_slots > len(pool):
        raise RecursiveSplitError("queue claims exceed CPU capacity")
    return dict(queue)


def _reseal_queue(unsigned: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(unsigned)
    value["status"] = _queue_status_from_items(value["items"])
    return seal(value, "queue_sha256")


def _atomic_write_queue(path: Path, queue: Mapping[str, Any]) -> None:
    _validate_queue(queue)
    payload = canonical_bytes(queue) + b"\n"
    if len(payload) > MAX_JSON_BYTES:
        raise RecursiveSplitError("queue JSON exceeds size cap")
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{secrets.token_hex(8)}.tmp")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
    fd: int | None = None
    try:
        fd = os.open(temporary, flags, 0o600)
        view = memoryview(payload)
        while view:
            written = os.write(fd, view)
            if written <= 0:
                raise RecursiveSplitError("short queue publication")
            view = view[written:]
        os.fsync(fd)
        os.close(fd)
        fd = None
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    except OSError as exc:
        raise RecursiveSplitError("cannot atomically publish queue") from exc
    finally:
        if fd is not None:
            with contextlib.suppress(OSError):
                os.close(fd)
        with contextlib.suppress(FileNotFoundError):
            temporary.unlink()


def load_split_queue(path: Path | str) -> dict[str, Any]:
    target = _queue_path(path)
    try:
        info = target.lstat()
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
            raise RecursiveSplitError("queue file is not a regular file")
        if info.st_uid != os.geteuid() or info.st_nlink != 1 or info.st_size > MAX_JSON_BYTES:
            raise RecursiveSplitError("queue file metadata is unsafe")
        # Read through an fd and verify identity/size before and after.  This
        # prevents a concurrent atomic replace (or an in-place corruption)
        # from being accepted as a valid queue snapshot.
        fd = os.open(target, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
        try:
            before = os.fstat(fd)
            if (
                before.st_dev != info.st_dev or before.st_ino != info.st_ino
                or before.st_size != info.st_size
            ):
                raise RecursiveSplitError("queue changed before read")
            chunks: list[bytes] = []
            observed = 0
            while True:
                chunk = os.read(fd, 1 << 20)
                if not chunk:
                    break
                observed += len(chunk)
                if observed > MAX_JSON_BYTES:
                    raise RecursiveSplitError("queue file exceeds size cap")
                chunks.append(chunk)
            after = os.fstat(fd)
        finally:
            os.close(fd)
        if (
            before.st_dev != after.st_dev or before.st_ino != after.st_ino
            or before.st_size != after.st_size or observed != before.st_size
        ):
            raise RecursiveSplitError("queue changed while reading")
        payload = b"".join(chunks)
    except OSError as exc:
        raise RecursiveSplitError("cannot read split queue") from exc
    try:
        raw = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RecursiveSplitError("split queue JSON is malformed") from exc
    if type(raw) is not dict or payload not in {canonical_bytes(raw), canonical_bytes(raw) + b"\n"}:
        raise RecursiveSplitError("split queue is not canonical JSON")
    return _validate_queue(raw)


def new_split_queue(
    split_manifest: Mapping[str, Any],
    *,
    cpu_pool: Sequence[int],
    queue_id: str | None = None,
    parent_manifest_sha256: str | None = None,
    default_cpu_slots: int = 1,
    lease_seconds: float = QUEUE_LEASE_SECONDS,
    now: float | None = None,
) -> dict[str, Any]:
    """Create an unclaimed queue for every authenticated split leaf."""

    if type(split_manifest) is not dict or not selfhash_valid(split_manifest, "manifest_sha256"):
        raise RecursiveSplitError("cannot queue an unsealed split manifest")
    if set(split_manifest) - (MANIFEST_REQUIRED_FIELDS | MANIFEST_OPTIONAL_FIELDS):
        raise RecursiveSplitError("split manifest field set mismatch")
    if split_manifest.get("schema_version") != SCHEMA_VERSION or split_manifest.get("kind") != MODULE_KIND:
        raise RecursiveSplitError("split manifest schema/kind mismatch")
    # This shape check does not have parent bytes; callers that have the source
    # should run verify_cover first.  It still authenticates every leaf record
    # and prevents queueing a partial/aliased frontier.
    leaves = _leaf_by_path(split_manifest)
    policy = split_manifest.get("split_policy")
    fanout = validate_fanout(policy.get("fanout") if type(policy) is dict else None)
    expected_paths = frontier_paths(fanout)
    if [leaf.get("path") for leaf in split_manifest.get("leaves", [])] != expected_paths:
        raise RecursiveSplitError("split manifest frontier is not ordered")
    if parent_manifest_sha256 is None:
        # A queue without an authenticated parent ancestry can still be useful
        # for a local toy run, but it must be explicitly marked as absent and
        # never confused with a production parent binding.
        parent_manifest_sha256 = None
    elif not is_sha256(parent_manifest_sha256):
        raise RecursiveSplitError("parent manifest hash is invalid")
    pool = list(cpu_pool)
    if type(cpu_pool) not in {list, tuple} or any(
        type(cpu) is not int or cpu < 0 for cpu in pool
    ) or pool != sorted(set(pool)):
        raise RecursiveSplitError("cpu_pool must be a sorted unique list of non-negative IDs")
    if (
        type(default_cpu_slots) is not int
        or isinstance(default_cpu_slots, bool)
        or not 1 <= default_cpu_slots <= len(pool)
    ):
        raise RecursiveSplitError("default CPU slots are invalid")
    lease = _finite_nonnegative(lease_seconds, label="lease_seconds")
    if lease <= 0 or lease > QUEUE_MAX_LEASE_SECONDS:
        raise RecursiveSplitError("lease_seconds is outside bounds")
    timestamp = time.time() if now is None else _finite_timestamp(now, label="queue now")
    parent = split_manifest.get("parent")
    if type(parent) is not dict:
        raise RecursiveSplitError("split manifest parent binding is missing")
    parent_id = _safe_text(parent.get("parent_id"), label="parent_id", maximum=192)
    if queue_id is None:
        queue_id = f"{parent_id}:{split_manifest['manifest_sha256'][:16]}"
    _safe_text(queue_id, label="queue_id", maximum=192)
    items: list[dict[str, Any]] = []
    for path in expected_paths:
        leaf = leaves[path]
        items.append(seal({
            "item_id": f"{parent_id}:{path}",
            "parent_id": parent_id,
            "parent_manifest_sha256": parent_manifest_sha256,
            "split_manifest_sha256": split_manifest["manifest_sha256"],
            "leaf_id": leaf["leaf_id"],
            "leaf_sha256": leaf["leaf_sha256"],
            "path": path,
            "depth": leaf["depth"],
            "child_cnf_sha256": leaf["child_cnf_sha256"],
            "child_dimacs_sha256": leaf["child_dimacs_sha256"],
            "child_num_variables": leaf["child_num_variables"],
            "child_num_clauses": leaf["child_num_clauses"],
            "child_dimacs_bytes": leaf["child_dimacs_bytes"],
            "cpu_slots": default_cpu_slots,
            "cpu_ids": [],
            "state": "PENDING",
            "claim": None,
            "attempts": 0,
            "last_error": None,
            "certificate_sha256": None,
        }, "item_sha256"))
    queue = seal({
        "schema_version": QUEUE_SCHEMA_VERSION,
        "kind": QUEUE_KIND,
        "queue_id": queue_id,
        "parent_id": parent_id,
        "parent_manifest_sha256": parent_manifest_sha256,
        "split_manifest_sha256": split_manifest["manifest_sha256"],
        "ancestry_sha256": split_manifest.get("ancestry_sha256"),
        "fanout": fanout,
        "cpu_pool": sorted(set(pool)),
        "cpu_capacity": len(set(pool)),
        "default_cpu_slots": default_cpu_slots,
        "lease_seconds": float(lease),
        "created_at": timestamp,
        "updated_at": timestamp,
        "status": QUEUE_STATUS_OPEN,
        "items": items,
        "event_sequence": 0,
        "recovery_count": 0,
    }, "queue_sha256")
    return _validate_queue(queue)


def create_split_queue(
    path: Path | str, split_manifest: Mapping[str, Any], **kwargs: Any,
) -> dict[str, Any]:
    """Create and atomically publish a queue; never overwrite an existing one."""

    target = _queue_path(path)
    if target.exists():
        raise RecursiveSplitError("queue already exists")
    queue = new_split_queue(split_manifest, **kwargs)
    _ensure_queue_lock(target)
    # O_EXCL publication avoids replacing a queue created by a racing worker.
    payload = canonical_bytes(queue) + b"\n"
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(target, flags, 0o600)
        try:
            view = memoryview(payload)
            while view:
                written = os.write(fd, view)
                if written <= 0:
                    raise RecursiveSplitError("short queue publication")
                view = view[written:]
            os.fsync(fd)
        finally:
            os.close(fd)
        directory = os.open(target.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    except FileExistsError as exc:
        raise RecursiveSplitError("queue already exists") from exc
    except OSError as exc:
        raise RecursiveSplitError("cannot publish split queue") from exc
    return queue


def _queue_mutate(
    path: Path | str,
    mutator: Any,
) -> Any:
    target = _queue_path(path)
    lock = _ensure_queue_lock(target)
    with _exclusive_lock(lock, blocking=True):
        queue = load_split_queue(target)
        result, changed = mutator(queue)
        if changed:
            _atomic_write_queue(target, result)
        return result if result is not None else queue


def recover_split_queue(path: Path | str, *, now: float | None = None) -> dict[str, Any]:
    """Requeue claims whose durable lease expired after a crash."""

    timestamp = time.time() if now is None else _finite_timestamp(now, label="recovery now")

    def mutate(queue: dict[str, Any]) -> tuple[dict[str, Any], bool]:
        value = _queue_unsigned(queue)
        changed = False
        recovered = 0
        for item in value["items"]:
            claim = item.get("claim")
            if item["state"] != "CLAIMED" or type(claim) is not dict:
                continue
            if timestamp < claim["lease_expires_at"]:
                continue
            item_unsigned = _queue_item_unsigned(item)
            item_unsigned.update({
                "state": "PENDING", "cpu_ids": [], "claim": None,
                "attempts": item_unsigned["attempts"] + 1,
                "last_error": "LEASE_EXPIRED_RECOVERED",
            })
            item.clear()
            item.update(seal(item_unsigned, "item_sha256"))
            recovered += 1
            changed = True
        if not changed:
            return queue, False
        value["updated_at"] = timestamp
        value["event_sequence"] += recovered
        value["recovery_count"] += recovered
        return _reseal_queue(value), True

    return _queue_mutate(path, mutate)


def claim_queue_item(
    path: Path | str,
    *,
    worker_id: str,
    now: float | None = None,
    lease_seconds: float | None = None,
    cpu_slots: int | None = None,
) -> dict[str, Any] | None:
    """Atomically claim the first pending child with a disjoint CPU lease."""

    worker = _safe_worker_id(worker_id)
    timestamp = time.time() if now is None else _finite_timestamp(now, label="claim now")
    requested_lease = None if lease_seconds is None else _finite_nonnegative(lease_seconds, label="lease_seconds")
    if requested_lease is not None and not 0 < requested_lease <= QUEUE_MAX_LEASE_SECONDS:
        raise RecursiveSplitError("claim lease_seconds is outside bounds")
    token_holder: dict[str, Any] = {}

    def mutate(queue: dict[str, Any]) -> tuple[dict[str, Any], bool]:
        # Recover expired claims in the same lock acquisition, so a claim can
        # never race a separate recovery pass.
        value = _queue_unsigned(queue)
        recovered = 0
        for item in value["items"]:
            claim = item.get("claim")
            if item["state"] == "CLAIMED" and type(claim) is dict and timestamp >= claim["lease_expires_at"]:
                unsigned = _queue_item_unsigned(item)
                unsigned.update({
                    "state": "PENDING", "cpu_ids": [], "claim": None,
                    "attempts": unsigned["attempts"] + 1,
                    "last_error": "LEASE_EXPIRED_RECOVERED",
                })
                item.clear()
                item.update(seal(unsigned, "item_sha256"))
                recovered += 1
        if recovered:
            value["recovery_count"] += recovered
            value["event_sequence"] += recovered
        occupied = {
            cpu
            for item in value["items"] if item["state"] == "CLAIMED"
            for cpu in item["cpu_ids"]
        }
        chosen: dict[str, Any] | None = None
        for item in value["items"]:
            if item["state"] != "PENDING":
                continue
            need = item["cpu_slots"] if cpu_slots is None else cpu_slots
            if type(need) is not int or need != item["cpu_slots"]:
                raise RecursiveSplitError("requested CPU slots do not match queue item")
            available = [cpu for cpu in value["cpu_pool"] if cpu not in occupied]
            if len(available) < need:
                continue
            ids = available[:need]
            duration = float(value["lease_seconds"] if requested_lease is None else requested_lease)
            claim = {
                "worker_id": worker,
                "token": secrets.token_hex(32),
                "claimed_at": timestamp,
                "lease_expires_at": timestamp + duration,
                "cpu_slots": need,
                "cpu_ids": ids,
            }
            unsigned = _queue_item_unsigned(item)
            unsigned.update({"state": "CLAIMED", "claim": claim, "cpu_ids": ids})
            item.clear()
            item.update(seal(unsigned, "item_sha256"))
            chosen = item
            value["event_sequence"] += 1
            break
        if chosen is None and not recovered:
            return queue, False
        value["updated_at"] = timestamp
        result = _reseal_queue(value)
        if chosen is not None:
            token_holder.update({
                "queue_sha256": result["queue_sha256"],
                "item": json.loads(json.dumps(chosen)),
                "claim": json.loads(json.dumps(chosen["claim"])),
            })
        return result, True

    _queue_mutate(path, mutate)
    return token_holder or None


def _check_claim(item: Mapping[str, Any], worker_id: str, token: str) -> None:
    _safe_worker_id(worker_id)
    if type(token) is not str or re.fullmatch(r"[0-9a-f]{64}", token) is None:
        raise RecursiveSplitError("claim token is invalid")
    claim = item.get("claim")
    if item.get("state") != "CLAIMED" or type(claim) is not dict:
        raise RecursiveSplitError("queue item is not claimed")
    if claim.get("worker_id") != worker_id or claim.get("token") != token:
        raise RecursiveSplitError("claim owner/token mismatch")


def release_queue_item(
    path: Path | str,
    *,
    item_id: str,
    worker_id: str,
    token: str,
    now: float | None = None,
) -> dict[str, Any]:
    """Release a claim back to PENDING without certifying the child."""

    timestamp = time.time() if now is None else _finite_timestamp(now, label="release now")

    def mutate(queue: dict[str, Any]) -> tuple[dict[str, Any], bool]:
        value = _queue_unsigned(queue)
        item = next((candidate for candidate in value["items"] if candidate["item_id"] == item_id), None)
        if item is None:
            raise RecursiveSplitError("unknown queue item")
        _check_claim(item, worker_id, token)
        unsigned = _queue_item_unsigned(item)
        unsigned.update({
            "state": "PENDING", "claim": None, "cpu_ids": [],
            "last_error": "RELEASED_BY_WORKER",
        })
        item.clear()
        item.update(seal(unsigned, "item_sha256"))
        value["updated_at"] = timestamp
        value["event_sequence"] += 1
        return _reseal_queue(value), True

    return _queue_mutate(path, mutate)


def renew_queue_item(
    path: Path | str,
    *,
    item_id: str,
    worker_id: str,
    token: str,
    lease_seconds: float | None = None,
    now: float | None = None,
) -> dict[str, Any]:
    """Extend one live queue claim without changing its CPU assignment.

    Recursive children can legitimately run longer than the initial dispatch
    interval.  A worker therefore renews its own still-live claim before the
    expiry boundary.  Renewal after expiry is intentionally refused: that
    claim may already have been recovered and reassigned to another worker.
    """

    timestamp = time.time() if now is None else _finite_timestamp(now, label="renewal now")
    requested = None if lease_seconds is None else _finite_nonnegative(
        lease_seconds, label="lease_seconds",
    )
    if requested is not None and not 0 < requested <= QUEUE_MAX_LEASE_SECONDS:
        raise RecursiveSplitError("renewal lease_seconds is outside bounds")

    def mutate(queue: dict[str, Any]) -> tuple[dict[str, Any], bool]:
        value = _queue_unsigned(queue)
        item = next((candidate for candidate in value["items"] if candidate["item_id"] == item_id), None)
        if item is None:
            raise RecursiveSplitError("unknown queue item")
        _check_claim(item, worker_id, token)
        claim = item["claim"]
        if timestamp >= claim["lease_expires_at"]:
            raise RecursiveSplitError("cannot renew an expired queue claim")
        duration = float(value["lease_seconds"] if requested is None else requested)
        renewed_claim = dict(claim)
        renewed_claim["lease_expires_at"] = timestamp + duration
        unsigned = _queue_item_unsigned(item)
        unsigned["claim"] = renewed_claim
        item.clear()
        item.update(seal(unsigned, "item_sha256"))
        value["updated_at"] = timestamp
        value["event_sequence"] += 1
        return _reseal_queue(value), True

    return _queue_mutate(path, mutate)


def _certificate_digest(certificate: Mapping[str, Any]) -> str:
    if type(certificate) is not dict:
        raise RecursiveSplitError("certificate must be an object")
    stored = certificate.get("certificate_sha256", certificate.get("record_sha256"))
    if stored is None:
        raise RecursiveSplitError("certificate has no authenticated digest")
    field = "certificate_sha256" if "certificate_sha256" in certificate else "record_sha256"
    if not selfhash_valid(certificate, field):
        raise RecursiveSplitError("certificate self-hash is invalid")
    return stored


def _queue_certificate_complete(
    certificate: Mapping[str, Any], item: Mapping[str, Any], validation: Mapping[str, Any] | None,
) -> bool:
    if not _validate_certificate_payload(certificate, item):
        return False
    if validation is not None:
        return bool(
            type(validation) is dict
            and validation.get("valid") is True
            and validation.get("strict_proof_unsat") is True
            and validation.get("fresh_proof_replay") is True
            and validation.get("source_toolchain_fresh") is True
            and validation.get("failures") == []
        )
    return _certificate_is_complete(certificate)


def certify_queue_item(
    path: Path | str,
    *,
    item_id: str,
    worker_id: str,
    token: str,
    certificate: Mapping[str, Any],
    validation: Mapping[str, Any] | None = None,
    now: float | None = None,
) -> dict[str, Any]:
    """Mark one child CERTIFIED only after strict proof evidence is present."""

    timestamp = time.time() if now is None else _finite_timestamp(now, label="certification now")

    def mutate(queue: dict[str, Any]) -> tuple[dict[str, Any], bool]:
        value = _queue_unsigned(queue)
        item = next((candidate for candidate in value["items"] if candidate["item_id"] == item_id), None)
        if item is None:
            raise RecursiveSplitError("unknown queue item")
        _check_claim(item, worker_id, token)
        if not _queue_certificate_complete(certificate, item, validation):
            raise RecursiveSplitError("certificate is not a complete fresh proof replay")
        digest = _certificate_digest(certificate)
        unsigned = _queue_item_unsigned(item)
        unsigned.update({
            "state": "CERTIFIED", "claim": None, "cpu_ids": [],
            "certificate_sha256": digest, "last_error": None,
        })
        item.clear()
        item.update(seal(unsigned, "item_sha256"))
        value["updated_at"] = timestamp
        value["event_sequence"] += 1
        return _reseal_queue(value), True

    return _queue_mutate(path, mutate)


def fail_queue_item(
    path: Path | str,
    *,
    item_id: str,
    worker_id: str,
    token: str,
    error: str,
    now: float | None = None,
) -> dict[str, Any]:
    """Record a terminal worker failure and release its CPU lease."""

    message = _safe_text(error, label="queue failure", maximum=2048)
    timestamp = time.time() if now is None else _finite_timestamp(now, label="failure now")

    def mutate(queue: dict[str, Any]) -> tuple[dict[str, Any], bool]:
        value = _queue_unsigned(queue)
        item = next((candidate for candidate in value["items"] if candidate["item_id"] == item_id), None)
        if item is None:
            raise RecursiveSplitError("unknown queue item")
        _check_claim(item, worker_id, token)
        unsigned = _queue_item_unsigned(item)
        unsigned.update({"state": "FAILED", "claim": None, "cpu_ids": [], "last_error": message})
        item.clear()
        item.update(seal(unsigned, "item_sha256"))
        value["updated_at"] = timestamp
        value["event_sequence"] += 1
        return _reseal_queue(value), True

    return _queue_mutate(path, mutate)


def split_queue_status(path: Path | str) -> dict[str, Any]:
    """Return a sealed, read-only queue progress summary."""

    queue = load_split_queue(path)
    items = queue["items"]
    counts = {state: sum(item["state"] == state for item in items) for state in sorted(QUEUE_ITEM_STATES)}
    claimed = sum(item["cpu_slots"] for item in items if item["state"] == "CLAIMED")
    return seal({
        "schema_version": QUEUE_SCHEMA_VERSION,
        "kind": "paper400-dic5-recursive-split-queue-status-v1",
        "queue_id": queue["queue_id"],
        "queue_sha256": queue["queue_sha256"],
        "split_manifest_sha256": queue["split_manifest_sha256"],
        "fanout": queue["fanout"],
        "status": queue["status"],
        "item_counts": counts,
        "certified_count": counts["CERTIFIED"],
        "pending_count": counts["PENDING"],
        "claimed_count": counts["CLAIMED"],
        "failed_count": counts["FAILED"],
        "cpu_capacity": queue["cpu_capacity"],
        "cpu_claimed": claimed,
        "cpu_available": queue["cpu_capacity"] - claimed,
        "event_sequence": queue["event_sequence"],
        "recovery_count": queue["recovery_count"],
        "scientific_claim": False,
    }, "record_sha256")


# Descriptive aliases make the persistence API easy to discover without
# creating a second schema or implementation.
initialize_split_queue = create_split_queue
load_queue = load_split_queue
recover_queue = recover_split_queue
claim_split_queue_item = claim_queue_item
release_split_queue_item = release_queue_item
renew_split_queue_item = renew_queue_item
certify_split_queue_item = certify_queue_item
complete_queue_item = certify_queue_item
fail_split_queue_item = fail_queue_item
queue_status = split_queue_status


# ---------------------------------------------------------------------------
# Proof aggregation and guarded cleanup


def _certificate_leaf_binding(certificate: Mapping[str, Any]) -> tuple[str | None, str | None]:
    leaf_id = certificate.get("leaf_id", certificate.get("child_id"))
    leaf_hash = certificate.get(
        "leaf_sha256",
        certificate.get("child_sha256", certificate.get("descendant_sha256")),
    )
    return leaf_id if type(leaf_id) is str else None, leaf_hash if is_sha256(leaf_hash) else None


def _certificate_is_complete(certificate: Mapping[str, Any]) -> bool:
    if type(certificate) is not dict:
        return False
    return bool(
        certificate.get("valid") is True
        and certificate.get("strict_proof_unsat") is True
        and (
            certificate.get("proof_replay_complete") is True
            or certificate.get("proof_replay_decision_complete") is True
            or certificate.get("fresh_proof_replay") is True
        )
        and certificate.get("hardness_only", False) is not True
        and certificate.get("solver_terminal_claim", True) is not False
    )


def aggregate_child_certificates(
    manifest: Mapping[str, Any], certificates: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """Derive parent UNSAT only from one complete certificate per leaf."""

    # Verify the structural manifest from the leaf metadata.  The caller may
    # have no parent bytes at this layer, so the self-hash and shape checks are
    # repeated here; ``verify_cover`` remains the stronger byte-level API.
    if type(manifest) is not dict or not selfhash_valid(manifest, "manifest_sha256"):
        raise RecursiveSplitError("cannot aggregate an unsealed split manifest")
    if (
        not MANIFEST_REQUIRED_FIELDS.issubset(manifest)
        or set(manifest) - (MANIFEST_REQUIRED_FIELDS | MANIFEST_OPTIONAL_FIELDS)
    ):
        raise RecursiveSplitError("split manifest field set mismatch")
    # Validate the exact frontier identities before accepting any certificate.
    # In particular, a certificate must carry the leaf-record hash generated
    # by this manifest; a bare ``leaf_id`` or a child-CNF hash is insufficient.
    leaves = _leaf_by_path(manifest)
    binding = manifest.get("certificate_binding")
    if (
        type(binding) is not dict
        or binding.get("method") != "exact-frontier-leaf-record-sha256-v1"
        or binding.get("leaf_identity_fields") != ["leaf_id", "leaf_sha256"]
        or binding.get("expected_certificate_count") != len(leaves)
        or binding.get("certificate_must_bind_child_cnf") is not True
        or binding.get("timeout_is_not_certificate") is not True
        or binding.get("leaf_sha256_sequence_sha256") != canonical_sha256([
            leaf["leaf_sha256"] for leaf in leaves.values()
        ])
    ):
        raise RecursiveSplitError("certificate binding policy is not authenticated")
    expected = {
        (leaf.get("leaf_id"), leaf.get("leaf_sha256")): leaf
        for leaf in leaves.values()
    }
    if len(expected) != len(leaves):
        raise RecursiveSplitError("split leaves have duplicate identity")
    if type(certificates) not in {list, tuple}:
        raise RecursiveSplitError("certificates must be a sequence")
    seen: set[tuple[str | None, str | None]] = set()
    records: list[dict[str, Any]] = []
    for position, certificate in enumerate(certificates):
        if type(certificate) is not dict:
            certificate = {}
        leaf_id, leaf_hash = _certificate_leaf_binding(certificate)
        key = (leaf_id, leaf_hash)
        valid_binding = key in expected and key not in seen
        complete = (
            valid_binding
            and _validate_certificate_payload(certificate, expected[key])
            and _certificate_is_complete(certificate)
        )
        if valid_binding:
            seen.add(key)
        records.append({
            "input_position": position,
            "leaf_id": leaf_id,
            "leaf_sha256": leaf_hash,
            "binding_valid": valid_binding,
            "proof_complete": complete,
            "certificate_sha256": certificate.get("certificate_sha256", certificate.get("record_sha256")),
        })
    all_complete = len(seen) == len(expected) and len(records) == len(expected) and all(
        item["proof_complete"] for item in records
    )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-recursive-parent-proof-aggregate-v1",
        "split_manifest_sha256": manifest.get("manifest_sha256"),
        "fanout": manifest.get("split_policy", {}).get("fanout"),
        "expected_child_count": len(expected),
        "observed_certificate_count": len(certificates),
        "all_child_indices_exactly_once": len(seen) == len(expected) and len(records) == len(expected),
        "all_children_proof_carrying_unsat": all_complete,
        "status": "PARENT_CUBE_UNSAT" if all_complete else "UNRESOLVED",
        "parent_cube_unsat": all_complete,
        "child_records": records,
        "claim_scope": "one-recursively-split-parent-cube-only",
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
        "hardness_timeout_is_not_unsat": True,
    }, "aggregate_sha256")


def _safe_owned_directory(path: Path) -> Path:
    target = Path(path)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise RecursiveSplitError("cleanup root must be a normalized absolute path")
    try:
        lexical = target.lstat()
        resolved = target.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise RecursiveSplitError("cleanup root is unavailable") from exc
    if (
        resolved != target or stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISDIR(lexical.st_mode)
        or lexical.st_uid != os.geteuid()
        or stat.S_IMODE(lexical.st_mode) != 0o700
    ):
        raise RecursiveSplitError("cleanup root must be an owned mode-0700 directory")
    return target


@contextlib.contextmanager
def _exclusive_lock(path: Path, *, blocking: bool = False):
    try:
        fd = os.open(path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    except OSError as exc:
        raise RecursiveSplitError(f"cannot open cleanup lock: {path}") from exc
    try:
        try:
            flags = fcntl.LOCK_EX if blocking else (fcntl.LOCK_EX | fcntl.LOCK_NB)
            fcntl.flock(fd, flags)
        except BlockingIOError as exc:
            raise RecursiveSplitError("exclusive lock is held by another process") from exc
        except OSError as exc:
            raise RecursiveSplitError("cannot acquire exclusive lock") from exc
        yield
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _proc_identity_alive(pid: int, start_ticks: int) -> bool:
    """Return true only when ``pid`` still has the recorded Linux identity."""

    try:
        payload = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
        close = payload.rfind(")")
        fields = payload[close + 2:].split() if close > 0 else []
        return bool(
            fields and fields[0] != "Z" and len(fields) > 19
            and int(fields[19]) == start_ticks
        )
    except (OSError, UnicodeDecodeError, ValueError):
        return False


def _live_generation_identities(runtime: Path) -> list[dict[str, int]]:
    """Scan every committed generation and return still-live identities."""

    live: list[dict[str, int]] = []
    generations = runtime / "generations"
    if not generations.exists():
        return live
    if generations.is_symlink() or not generations.is_dir():
        raise RecursiveSplitError("runtime generation tree is malformed")
    for generation in sorted(generations.iterdir(), key=lambda path: path.name):
        if generation.is_symlink() or not generation.is_dir():
            raise RecursiveSplitError("runtime generation tree is malformed")
        for name in ("start.commit.json", "resume.commit.json"):
            path = generation / name
            if not path.exists():
                continue
            if path.is_symlink() or not path.is_file():
                raise RecursiveSplitError("runtime commit is aliased")
            try:
                value = json.loads(path.read_text(encoding="ascii"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise RecursiveSplitError("runtime commit is unreadable") from exc
            pid = value.get("pid")
            ticks = value.get("proc_start_ticks")
            if type(pid) is int and type(ticks) is int and pid > 0 and ticks >= 0:
                if _proc_identity_alive(pid, ticks):
                    identity = {"pid": pid, "proc_start_ticks": ticks}
                    if identity not in live:
                        live.append(identity)
    return live


def _cleanup_entry_manifest(runtime: Path) -> dict[str, Any]:
    """Capture a conservative, inode-bound manifest of a transport tree."""
    entries: list[dict[str, Any]] = []
    if runtime.is_symlink() or not runtime.is_dir():
        raise RecursiveSplitError("cleanup runtime is not a plain directory")
    for candidate in sorted(runtime.rglob("*"), key=lambda item: item.relative_to(runtime).as_posix()):
        relative = candidate.relative_to(runtime).as_posix()
        info = candidate.lstat()
        if info.st_uid != os.geteuid():
            raise RecursiveSplitError("cleanup entry ownership is unsafe")
        if stat.S_ISLNK(info.st_mode):
            raise RecursiveSplitError("refusing to authorize symlink cleanup entry")
        if stat.S_ISDIR(info.st_mode):
            # Directory link counts naturally include ``.`` and every direct
            # subdirectory; unlike a regular-file hardlink count they are not
            # expected to be one.  The complete tree manifest below freezes
            # this value before removal, so a later tree mutation is still
            # rejected by the claim/commit comparison.
            if info.st_nlink < 2:
                raise RecursiveSplitError("cleanup directory link count is unsafe")
            kind = "directory"
            size = 0
        elif stat.S_ISREG(info.st_mode):
            if info.st_nlink != 1:
                raise RecursiveSplitError("cleanup file link count is unsafe")
            kind = "file"
            size = info.st_size
        else:
            raise RecursiveSplitError("cleanup entry is not a regular file/directory")
        entries.append({
            "relative_path": relative,
            "entry_type": kind,
            "device": int(info.st_dev),
            "inode": int(info.st_ino),
            "mode": stat.S_IMODE(info.st_mode),
            "uid": int(info.st_uid),
            "links": int(info.st_nlink),
            "bytes": int(size),
        })
        if len(entries) > CLEANUP_MAX_ENTRIES:
            raise RecursiveSplitError("cleanup tree has too many entries")
    return {
        "relative_path": "runtime/dmtcp",
        "entries": entries,
        "entry_count": len(entries),
        "regular_file_bytes": sum(item["bytes"] for item in entries if item["entry_type"] == "file"),
        "manifest_sha256": canonical_sha256(entries),
    }


def _publish_cleanup_record(path: Path, record: Mapping[str, Any], *, exclusive: bool = True) -> None:
    payload = canonical_bytes(dict(record)) + b"\n"
    flags = os.O_WRONLY | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW
    if exclusive:
        flags |= os.O_EXCL
    fd = os.open(path, flags, 0o600)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(fd, view)
            if written <= 0:
                raise RecursiveSplitError("short cleanup record publication")
            view = view[written:]
        os.fsync(fd)
    finally:
        os.close(fd)
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def _read_cleanup_record(path: Path, *, field: str, kind: str) -> dict[str, Any]:
    try:
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode) or info.st_uid != os.geteuid():
            raise RecursiveSplitError("cleanup record metadata is unsafe")
        payload = path.read_bytes()
        value = json.loads(payload)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RecursiveSplitError("cleanup record is unreadable") from exc
    if type(value) is not dict or payload not in {canonical_bytes(value), canonical_bytes(value) + b"\n"}:
        raise RecursiveSplitError("cleanup record is not canonical")
    if value.get("kind") != kind or not selfhash_valid(value, field):
        raise RecursiveSplitError("cleanup record self-hash/kind is invalid")
    return value


def _cleanup_claim_value(root: Path, split_manifest: Mapping[str, Any], aggregate: Mapping[str, Any], manifest: Mapping[str, Any]) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": CLEANUP_CLAIM_KIND,
        "parent_root": str(root),
        "runtime_relative_path": "runtime/dmtcp",
        "aggregate_sha256": aggregate["aggregate_sha256"],
        "split_manifest_sha256": split_manifest["manifest_sha256"],
        "transport_manifest": manifest,
        "irreversible": True,
    }, "cleanup_claim_sha256")


def _cleanup_commit_value(root: Path, claim: Mapping[str, Any], manifest: Mapping[str, Any]) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": CLEANUP_COMMIT_KIND,
        "parent_root": str(root),
        "runtime_relative_path": "runtime/dmtcp",
        "cleanup_claim_sha256": claim["cleanup_claim_sha256"],
        "transport_manifest_sha256": manifest["manifest_sha256"],
        "removed_entries": manifest["entry_count"],
        "removed_regular_file_bytes": manifest["regular_file_bytes"],
        "runtime_absent": True,
        "irreversible": True,
    }, "cleanup_sha256")


def cleanup_parent_transport(
    parent_root: Path,
    *,
    split_manifest: Mapping[str, Any],
    aggregate: Mapping[str, Any],
    dry_run: bool = False,
) -> dict[str, Any]:
    """Delete only parent DMTCP transport after every child is certified.

    The parent static CNF, split manifest, trigger evidence, and all child
    proof records remain.  No deletion is attempted for an unresolved
    aggregate, a live solver, a symlinked runtime, or a missing exact lock.
    """

    if type(split_manifest) is not dict or not selfhash_valid(split_manifest, "manifest_sha256"):
        raise RecursiveSplitError("split manifest is not sealed")
    if type(aggregate) is not dict or not selfhash_valid(aggregate, "aggregate_sha256"):
        raise RecursiveSplitError("aggregate is not sealed")
    if aggregate.get("split_manifest_sha256") != split_manifest.get("manifest_sha256"):
        raise RecursiveSplitError("aggregate/manifest binding mismatch")
    if aggregate.get("parent_cube_unsat") is not True or aggregate.get("status") != "PARENT_CUBE_UNSAT":
        raise RecursiveSplitError("parent transport is not eligible for cleanup")
    root = _safe_owned_directory(Path(parent_root))
    lock_path = root / ".hierarchical-resume.lock"
    runtime = root / "runtime" / "dmtcp"
    cleanup_claim_path = root / CLEANUP_CLAIM_NAME
    cleanup_commit_path = root / CLEANUP_COMMIT_NAME
    if cleanup_commit_path.exists():
        commit = _read_cleanup_record(
            cleanup_commit_path, field="cleanup_sha256", kind=CLEANUP_COMMIT_KIND,
        )
        if runtime.exists() or commit.get("runtime_absent") is not True:
            raise RecursiveSplitError("cleanup commit/runtime state mismatch")
        return commit
    if cleanup_claim_path.exists():
        claim = _read_cleanup_record(
            cleanup_claim_path, field="cleanup_claim_sha256", kind=CLEANUP_CLAIM_KIND,
        )
        if (
            claim.get("parent_root") != str(root)
            or claim.get("aggregate_sha256") != aggregate["aggregate_sha256"]
            or claim.get("split_manifest_sha256") != split_manifest["manifest_sha256"]
        ):
            raise RecursiveSplitError("cleanup claim binding mismatch")
        manifest = claim.get("transport_manifest")
        if type(manifest) is not dict or manifest.get("manifest_sha256") != canonical_sha256(manifest.get("entries")):
            raise RecursiveSplitError("cleanup claim transport manifest is invalid")
    else:
        if not runtime.exists() or runtime.is_symlink() or not runtime.is_dir():
            raise RecursiveSplitError("parent DMTCP runtime is absent or aliased")
        manifest = _cleanup_entry_manifest(runtime)
    # A committed active session is not enough: inspect every generation PID
    # and reject any identity that is still alive.  This is intentionally
    # conservative; a stale PID record causes a no-op rather than deletion.
    live = _live_generation_identities(runtime)
    if live:
        raise RecursiveSplitError("parent solver identity is still alive")
    if dry_run:
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-parent-transport-cleanup-plan-v1",
            "parent_root": str(root),
            "runtime_relative_path": "runtime/dmtcp",
            "eligible": True,
            "applied": False,
            "dry_run": True,
            "removed_entries": [],
            "aggregate_sha256": aggregate["aggregate_sha256"],
            "transport_manifest_sha256": manifest["manifest_sha256"],
        }, "cleanup_sha256")
    with _exclusive_lock(lock_path):
        # Re-check the runtime after taking the lock.  No external process may
        # start/resume the old parent while deletion is in progress.  The
        # pre-lock snapshot is intentionally discarded: a PID can be reused
        # or a new generation can appear in the race window.
        if cleanup_commit_path.exists():
            return _read_cleanup_record(
                cleanup_commit_path, field="cleanup_sha256", kind=CLEANUP_COMMIT_KIND,
            )
        live_after_lock = _live_generation_identities(runtime) if runtime.exists() else []
        if live_after_lock:
            raise RecursiveSplitError("parent solver became live before cleanup")
        if not cleanup_claim_path.exists():
            if not runtime.exists():
                raise RecursiveSplitError("cleanup runtime disappeared before claim")
            # Re-capture under the lock to bind exactly the bytes/inodes that
            # will be removed, then durably publish the claim before deletion.
            manifest = _cleanup_entry_manifest(runtime)
            claim = _cleanup_claim_value(root, split_manifest, aggregate, manifest)
            _publish_cleanup_record(cleanup_claim_path, claim)
        else:
            claim = _read_cleanup_record(
                cleanup_claim_path, field="cleanup_claim_sha256", kind=CLEANUP_CLAIM_KIND,
            )
            manifest = claim["transport_manifest"]
        if runtime.exists():
            current = _cleanup_entry_manifest(runtime)
            if current["manifest_sha256"] != manifest["manifest_sha256"]:
                raise RecursiveSplitError("transport changed after cleanup claim")
            shutil.rmtree(runtime)
            parent_dir = runtime.parent
            directory = os.open(parent_dir, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
            try:
                os.fsync(directory)
            finally:
                os.close(directory)
        elif not cleanup_claim_path.exists():
            raise RecursiveSplitError("cleanup claim is missing")
        commit = _cleanup_commit_value(root, claim, manifest)
        _publish_cleanup_record(cleanup_commit_path, commit)
        return _read_cleanup_record(
            cleanup_commit_path, field="cleanup_sha256", kind=CLEANUP_COMMIT_KIND,
        )


__all__ = [
    "DEFAULT_FANOUT", "DEFAULT_MAX_SPLITS_PER_PASS", "MAX_FANOUT",
    "MODULE_KIND", "SCHEMA_VERSION", "SOLVER_TIMEOUT_SECONDS",
    "SUPPORTED_FANOUTS", "RecursiveSplitError", "aggregate_child_certificates",
    "build_binary_cover", "build_split_manifest", "build_timeout_evidence",
    "canonical_bytes", "canonical_sha256", "choose_split_variables",
    "effective_solver_seconds", "fanout_depth", "frontier_paths",
    "observe_proc_cpu_seconds",
    "is_sha256", "new_timing_ledger", "parse_dimacs", "render_dimacs",
    "render_leaf_payload", "seal", "selfhash_valid", "structural_cnf_sha256",
    "timeout_reached", "should_split_for_timeout", "split_plan",
    "update_timing_ledger", "validate_fanout", "verify_cover",
    "cleanup_parent_transport", "split_factor_for_cpu",
    "fanout_for_available_cpus",
    "QUEUE_SCHEMA_VERSION", "QUEUE_KIND", "QUEUE_ITEM_STATES",
    "QUEUE_TERMINAL_STATES", "QUEUE_STATUS_OPEN", "QUEUE_STATUS_COMPLETE",
    "QUEUE_STATUS_FAILED", "QUEUE_LEASE_SECONDS", "QUEUE_MAX_LEASE_SECONDS",
    "new_split_queue", "create_split_queue", "initialize_split_queue",
    "load_split_queue", "load_queue", "recover_split_queue", "recover_queue",
    "claim_queue_item", "claim_split_queue_item", "release_queue_item",
    "release_split_queue_item", "renew_queue_item", "renew_split_queue_item",
    "certify_queue_item", "certify_split_queue_item",
    "complete_queue_item", "fail_queue_item", "fail_split_queue_item",
    "split_queue_status", "queue_status",
]
