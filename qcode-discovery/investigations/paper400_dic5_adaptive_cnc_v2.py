#!/usr/bin/env python3
"""Strict, solver-free adaptive lookahead cubing for paper400 materials.

This module is intentionally TEST_ONLY.  It parses and hashes a DIMACS CNF,
performs deterministic Boolean constraint propagation, and refines only paths
explicitly observed as ``UNKNOWN`` or ``TIMEOUT``.  A newly generated,
non-conflicting child for which no observation exists is a terminal
``PENDING`` frontier leaf; it is never silently treated as hard.

The lookahead ranking is a project-defined, March-inspired policy.  It first
prefers candidates with more conflicting polarities, then uses
``left * right + left + right`` where each gain includes the decision itself,
and finally chooses the smaller DIMACS variable.  It is not claimed to be a
byte-for-byte reproduction of a particular March release.

Every split certifies only the propositional identity

    P <=> (P AND v) OR (P AND NOT v).

No solver or proof checker is invoked.  The output cannot authorize a
production launch or authenticate terminal SAT/UNSAT observations.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping, Sequence
from typing import Any


SCHEMA_VERSION = 2
MANIFEST_KIND = "paper400-dic5-adaptive-lookahead-cubes-v2"
COVER_FORMULATION = "recursive-binary-parent-cover-v2"
AUTHORITY_TEST_ONLY = "TEST_ONLY_ADAPTIVE_CUBER_V2"
SCORING_FORMULA = "left_gain*right_gain+left_gain+right_gain"
TIE_BREAK = (
    "descending-conflict-branch-count-then-descending-score-then-"
    "ascending-dimacs-variable-v1"
)
CONFLICT_PRIORITY = "descending-conflicting-polarity-count-before-score-v1"
SCORING_SCOPE = (
    "project-defined-march-inspired-not-exact-march-reproduction-v1"
)
HARD_STATUSES = frozenset({"UNKNOWN", "TIMEOUT"})
NON_HARD_STATUSES = frozenset({"SAT", "UNSAT"})
EXTERNAL_STATUSES = HARD_STATUSES | NON_HARD_STATUSES
BCP_CONFLICT_STATUS = "BCP_CONFLICT"
PENDING_STATUS = "PENDING"
DEFAULT_MAX_NODES = 4095
MAX_NODE_BUDGET = 1_000_000
MAX_DEPTH = 64

MANIFEST_FIELDS = frozenset({
    "schema_version",
    "manifest_kind",
    "cover_formulation",
    "authority",
    "test_only",
    "production_eligible",
    "launch_authorized",
    "source",
    "parent",
    "policy",
    "tree",
    "coverage",
    "claim_scope",
    "manifest_sha256",
})
SOURCE_FIELDS = frozenset({
    "source_cnf_sha256",
    "canonical_cnf_sha256",
    "clauses_sha256",
    "num_variables",
    "num_clauses",
})
PARENT_FIELDS = frozenset({
    "assumptions",
    "assumptions_sha256",
    "cube_sha256",
    "augmented_cnf_sha256",
    "augmented_clause_count",
})
POLICY_FIELDS = frozenset({
    "candidate_variables",
    "candidate_variables_sha256",
    "hard_statuses",
    "scoring_formula",
    "tie_break",
    "conflict_priority",
    "gain_definition",
    "gain_includes_decision",
    "positive_polarity_is_left",
    "scoring_scope",
    "max_depth",
    "max_nodes",
    "status_input_sha256",
})
BCP_FIELDS = frozenset({
    "method",
    "source_cnf_sha256",
    "clauses_sha256",
    "assumptions",
    "propagated_literals",
    "assignment",
    "assigned_variable_count",
    "conflict",
    "conflict_clause_index",
    "bcp_sha256",
})
RANKING_FIELDS = frozenset({
    "dimacs_variable",
    "left_literal",
    "right_literal",
    "left_gain",
    "right_gain",
    "left_conflict",
    "right_conflict",
    "conflict_branch_count",
    "left_bcp_sha256",
    "right_bcp_sha256",
    "score",
    "rank",
})
NODE_FIELDS = frozenset({
    "node_id",
    "path",
    "depth",
    "parent_node_id",
    "parent_cube_sha256",
    "edge_literal",
    "assumptions",
    "assumptions_sha256",
    "cube_sha256",
    "augmented_cnf_sha256",
    "augmented_clause_count",
    "observed_status",
    "status_source",
    "status_binding_sha256",
    "bcp",
    "candidate_ranking",
    "candidate_ranking_sha256",
    "selected_variable",
    "positive_child_id",
    "negative_child_id",
    "terminal_reason",
    "node_sha256",
})
COVER_CHILD_FIELDS = frozenset({
    "node_id", "decision_literal", "cube_sha256", "cnf_sha256",
})
COVER_FIELDS = frozenset({
    "parent_node_id",
    "parent_path",
    "parent_cube_sha256",
    "parent_cnf_sha256",
    "split_variable",
    "positive_child",
    "negative_child",
    "mutually_exclusive",
    "exhaustive",
    "identity",
    "cover_sha256",
})
TREE_FIELDS = frozenset({
    "root_node_id",
    "nodes",
    "local_covers",
    "node_sha256_sequence_sha256",
    "cover_sha256_sequence_sha256",
    "tree_sha256",
})
COVERAGE_FIELDS = frozenset({
    "relative_to_parent_cube_sha256",
    "internal_node_count",
    "terminal_leaf_count",
    "local_binary_cover_count",
    "terminal_leaf_cube_sha256_sequence_sha256",
    "variable_depth",
    "mutually_exclusive",
    "exhaustive",
    "proof_method",
})
CLAIM_SCOPE_FIELDS = frozenset({
    "solver_invoked",
    "terminal_statuses_authenticated_by_solver_proof",
    "establishes_only_partition_equivalence",
    "production_eligible",
    "launch_authorized",
})


class AdaptiveCubeError(RuntimeError):
    """A DIMACS input, adaptive policy, tree, or hash binding is invalid."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    result = dict(value)
    result.pop(field, None)
    result[field] = canonical_sha256(result)
    return result


def _is_sha256(value: Any) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        return bytes.fromhex(value).hex() == value
    except ValueError:
        return False


def selfhash_valid(value: Any, field: str) -> bool:
    if type(value) is not dict or not _is_sha256(value.get(field)):
        return False
    unsigned = dict(value)
    stored = unsigned.pop(field)
    try:
        return stored == canonical_sha256(unsigned)
    except (TypeError, ValueError, RecursionError):
        return False


def json_type_equal(left: Any, right: Any) -> bool:
    """Recursively compare JSON values without tuple/list or bool/int collapse."""

    if type(left) is not type(right):
        return False
    if type(left) is dict:
        if set(left) != set(right):
            return False
        return all(
            type(key) is str and json_type_equal(left[key], right[key])
            for key in left
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            json_type_equal(left_item, right_item)
            for left_item, right_item in zip(left, right)
        )
    return type(left) in {str, int, bool, type(None)} and left == right


def _plain_object(value: Any, fields: frozenset[str], label: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != fields:
        raise AdaptiveCubeError(f"{label} field set mismatch")
    return value


_UNSIGNED_DECIMAL = re.compile(r"(?:0|[1-9][0-9]*)\Z")
_SIGNED_DECIMAL = re.compile(r"(?:0|-?[1-9][0-9]*)\Z")
_PATH = re.compile(r"R[+-]*\Z")
_NODE_ID = re.compile(r"node-([0-9]{7})\Z")


def parse_dimacs(dimacs: bytes) -> dict[str, Any]:
    """Parse strict ASCII DIMACS with exact declared counts and termination."""

    if type(dimacs) is not bytes:
        raise AdaptiveCubeError("DIMACS input must be bytes")
    try:
        text = dimacs.decode("ascii", errors="strict")
    except UnicodeDecodeError as exc:
        raise AdaptiveCubeError("DIMACS input is not strict ASCII") from exc

    header: tuple[int, int] | None = None
    pending: list[int] = []
    clauses: list[list[int]] = []
    for line_number, raw_line in enumerate(text.splitlines(), 1):
        stripped = raw_line.strip()
        if not stripped:
            continue
        tokens = stripped.split()
        if tokens[0] == "c":
            if pending:
                raise AdaptiveCubeError(
                    f"comment interrupts clause at line {line_number}"
                )
            continue
        if tokens[0] == "p":
            if header is not None or pending or clauses:
                raise AdaptiveCubeError("DIMACS header is duplicate or misplaced")
            if (
                len(tokens) != 4
                or tokens[1] != "cnf"
                or _UNSIGNED_DECIMAL.fullmatch(tokens[2]) is None
                or _UNSIGNED_DECIMAL.fullmatch(tokens[3]) is None
            ):
                raise AdaptiveCubeError("DIMACS header must be exactly: p cnf N M")
            header = (int(tokens[2]), int(tokens[3]))
            continue
        if header is None:
            raise AdaptiveCubeError(
                f"clause data precedes DIMACS header at line {line_number}"
            )
        for token in tokens:
            if _SIGNED_DECIMAL.fullmatch(token) is None:
                raise AdaptiveCubeError(
                    f"invalid DIMACS integer token at line {line_number}"
                )
            literal = int(token)
            if literal == 0:
                clauses.append(pending)
                pending = []
            elif abs(literal) > header[0]:
                raise AdaptiveCubeError(
                    f"literal out of declared range at line {line_number}"
                )
            else:
                pending.append(literal)

    if header is None:
        raise AdaptiveCubeError("DIMACS header is missing")
    if pending:
        raise AdaptiveCubeError("final DIMACS clause is not terminated by 0")
    num_variables, num_clauses = header
    if len(clauses) != num_clauses:
        raise AdaptiveCubeError(
            f"declared {num_clauses} clauses but parsed {len(clauses)}"
        )
    parsed = {
        "num_variables": num_variables,
        "num_clauses": num_clauses,
        "clauses": clauses,
        "source_cnf_sha256": hashlib.sha256(dimacs).hexdigest(),
        "clauses_sha256": canonical_sha256(clauses),
    }
    parsed["canonical_cnf_sha256"] = hashlib.sha256(
        _render_parsed_dimacs(parsed, ())
    ).hexdigest()
    return parsed


def _validate_cube(
    assumptions: Sequence[int], num_variables: int, *, label: str,
) -> tuple[int, ...]:
    if isinstance(assumptions, (str, bytes)) or not isinstance(
        assumptions, Sequence
    ):
        raise AdaptiveCubeError(f"{label} must be a sequence of literals")
    result: list[int] = []
    seen: set[int] = set()
    for literal in assumptions:
        if (
            type(literal) is not int
            or literal == 0
            or not 1 <= abs(literal) <= num_variables
        ):
            raise AdaptiveCubeError(f"{label} contains an invalid literal")
        variable = abs(literal)
        if variable in seen:
            raise AdaptiveCubeError(f"{label} assigns a variable more than once")
        seen.add(variable)
        result.append(literal)
    return tuple(result)


def _render_parsed_dimacs(
    parsed: Mapping[str, Any], assumptions: Sequence[int],
) -> bytes:
    clauses = parsed["clauses"]
    lines = [
        f"p cnf {parsed['num_variables']} {len(clauses) + len(assumptions)}\n"
    ]
    lines.extend(" ".join(map(str, clause)) + " 0\n" for clause in clauses)
    lines.extend(f"{literal} 0\n" for literal in assumptions)
    return "".join(lines).encode("ascii")


def render_cube_dimacs(dimacs: bytes, assumptions: Sequence[int]) -> bytes:
    parsed = parse_dimacs(dimacs)
    cube = _validate_cube(
        assumptions, parsed["num_variables"], label="cube assumptions"
    )
    return _render_parsed_dimacs(parsed, cube)


def _cube_binding(parsed: Mapping[str, Any], cube: Sequence[int]) -> dict[str, Any]:
    return {
        "assumptions_sha256": canonical_sha256(list(cube)),
        "cube_sha256": canonical_sha256({
            "source_cnf_sha256": parsed["source_cnf_sha256"],
            "assumptions": list(cube),
        }),
        "augmented_cnf_sha256": hashlib.sha256(
            _render_parsed_dimacs(parsed, cube)
        ).hexdigest(),
        "augmented_clause_count": parsed["num_clauses"] + len(cube),
    }


def _remaining_literals(
    clause: Sequence[int], assignment: Mapping[int, bool],
) -> tuple[bool, tuple[int, ...]]:
    remaining: set[int] = set()
    for literal in clause:
        variable = abs(literal)
        if variable in assignment:
            if assignment[variable] == (literal > 0):
                return True, ()
        else:
            remaining.add(literal)
    if any(-literal in remaining for literal in remaining):
        return True, ()
    return False, tuple(sorted(remaining, key=lambda lit: (abs(lit), lit < 0)))


def _propagate_parsed(
    parsed: Mapping[str, Any], assumptions: Sequence[int],
) -> dict[str, Any]:
    cube = _validate_cube(
        assumptions, parsed["num_variables"], label="BCP assumptions"
    )
    assignment = {abs(literal): literal > 0 for literal in cube}
    propagated: list[int] = []
    conflict_clause_index: int | None = None
    while True:
        changed = False
        for clause_index, clause in enumerate(parsed["clauses"]):
            satisfied, remaining = _remaining_literals(clause, assignment)
            if satisfied:
                continue
            if not remaining:
                conflict_clause_index = clause_index
                break
            if len(remaining) == 1:
                literal = remaining[0]
                variable = abs(literal)
                value = literal > 0
                if variable in assignment:
                    if assignment[variable] != value:
                        conflict_clause_index = clause_index
                        break
                    continue
                assignment[variable] = value
                propagated.append(literal)
                changed = True
                break
        if conflict_clause_index is not None or not changed:
            break

    return seal({
        "method": "deterministic-clause-order-bcp-v2",
        "source_cnf_sha256": parsed["source_cnf_sha256"],
        "clauses_sha256": parsed["clauses_sha256"],
        "assumptions": list(cube),
        "propagated_literals": propagated,
        "assignment": [
            {"dimacs_variable": variable, "value": int(assignment[variable])}
            for variable in sorted(assignment)
        ],
        "assigned_variable_count": len(assignment),
        "conflict": conflict_clause_index is not None,
        "conflict_clause_index": conflict_clause_index,
    }, "bcp_sha256")


def deterministic_bcp(dimacs: bytes, assumptions: Sequence[int]) -> dict[str, Any]:
    return _propagate_parsed(parse_dimacs(dimacs), assumptions)


def _candidate_tuple(
    candidates: Sequence[int], num_variables: int, parent_cube: Sequence[int],
) -> tuple[int, ...]:
    if isinstance(candidates, (str, bytes)) or not isinstance(candidates, Sequence):
        raise AdaptiveCubeError("candidate variables must be a sequence")
    parent_variables = {abs(literal) for literal in parent_cube}
    result: set[int] = set()
    for variable in candidates:
        if type(variable) is not int or not 1 <= variable <= num_variables:
            raise AdaptiveCubeError("candidate variable is out of range")
        if variable in result:
            raise AdaptiveCubeError("candidate variables contain a duplicate")
        if variable in parent_variables:
            raise AdaptiveCubeError("candidate variable is fixed by the parent cube")
        result.add(variable)
    return tuple(sorted(result))


def _assignment_variables(bcp: Mapping[str, Any]) -> set[int]:
    return {record["dimacs_variable"] for record in bcp["assignment"]}


def _score_parsed(
    parsed: Mapping[str, Any], cube: Sequence[int], candidates: Sequence[int],
) -> list[dict[str, Any]]:
    base = _propagate_parsed(parsed, cube)
    if base["conflict"] is True:
        raise AdaptiveCubeError("cannot score candidates below a BCP conflict")
    base_variables = _assignment_variables(base)
    ranking: list[dict[str, Any]] = []
    for variable in candidates:
        if variable in base_variables:
            continue
        positive = _propagate_parsed(parsed, (*cube, variable))
        negative = _propagate_parsed(parsed, (*cube, -variable))
        left_gain = len(_assignment_variables(positive) - base_variables)
        right_gain = len(_assignment_variables(negative) - base_variables)
        conflict_count = int(positive["conflict"]) + int(negative["conflict"])
        ranking.append({
            "dimacs_variable": variable,
            "left_literal": variable,
            "right_literal": -variable,
            "left_gain": left_gain,
            "right_gain": right_gain,
            "left_conflict": positive["conflict"],
            "right_conflict": negative["conflict"],
            "conflict_branch_count": conflict_count,
            "left_bcp_sha256": positive["bcp_sha256"],
            "right_bcp_sha256": negative["bcp_sha256"],
            "score": left_gain * right_gain + left_gain + right_gain,
        })
    ranking.sort(key=lambda record: (
        -record["conflict_branch_count"],
        -record["score"],
        record["dimacs_variable"],
    ))
    return [
        {**record, "rank": rank}
        for rank, record in enumerate(ranking, 1)
    ]


def score_candidates(
    dimacs: bytes,
    assumptions: Sequence[int],
    candidate_variables: Sequence[int],
) -> list[dict[str, Any]]:
    parsed = parse_dimacs(dimacs)
    cube = _validate_cube(
        assumptions, parsed["num_variables"], label="score assumptions"
    )
    candidates = _candidate_tuple(
        candidate_variables, parsed["num_variables"], cube
    )
    return _score_parsed(parsed, cube, candidates)


def _strict_statuses(status_by_path: Mapping[str, str]) -> dict[str, str]:
    if type(status_by_path) is not dict:
        raise AdaptiveCubeError("status_by_path must be a plain object")
    result: dict[str, str] = {}
    for path, status in status_by_path.items():
        if type(path) is not str or _PATH.fullmatch(path) is None:
            raise AdaptiveCubeError("status path must match R[+-]*")
        if type(status) is not str or status not in EXTERNAL_STATUSES:
            raise AdaptiveCubeError("external leaf status is invalid")
        result[path] = status
    return result


def _node_number(node_id: str) -> int:
    match = _NODE_ID.fullmatch(node_id) if type(node_id) is str else None
    if match is None:
        raise AdaptiveCubeError("node id is malformed")
    return int(match.group(1))


def _cover_record(
    parent: Mapping[str, Any],
    positive: Mapping[str, Any],
    negative: Mapping[str, Any],
) -> dict[str, Any]:
    variable = parent["selected_variable"]
    return seal({
        "parent_node_id": parent["node_id"],
        "parent_path": parent["path"],
        "parent_cube_sha256": parent["cube_sha256"],
        "parent_cnf_sha256": parent["augmented_cnf_sha256"],
        "split_variable": variable,
        "positive_child": {
            "node_id": positive["node_id"],
            "decision_literal": variable,
            "cube_sha256": positive["cube_sha256"],
            "cnf_sha256": positive["augmented_cnf_sha256"],
        },
        "negative_child": {
            "node_id": negative["node_id"],
            "decision_literal": -variable,
            "cube_sha256": negative["cube_sha256"],
            "cnf_sha256": negative["augmented_cnf_sha256"],
        },
        "mutually_exclusive": True,
        "exhaustive": True,
        "identity": "P <=> (P AND v) OR (P AND NOT v)",
    }, "cover_sha256")


def _coverage_record(
    nodes: Sequence[Mapping[str, Any]],
    covers: Sequence[Mapping[str, Any]],
    parent_cube_sha256: str,
) -> dict[str, Any]:
    leaves = [node for node in nodes if node["terminal_reason"] is not None]
    internal = [node for node in nodes if node["terminal_reason"] is None]
    return {
        "relative_to_parent_cube_sha256": parent_cube_sha256,
        "internal_node_count": len(internal),
        "terminal_leaf_count": len(leaves),
        "local_binary_cover_count": len(covers),
        "terminal_leaf_cube_sha256_sequence_sha256": canonical_sha256([
            node["cube_sha256"] for node in leaves
        ]),
        "variable_depth": len({node["depth"] for node in leaves}) > 1,
        "mutually_exclusive": True,
        "exhaustive": True,
        "proof_method": "recursive-binary-cover-induction-v2",
    }


def build_adaptive_manifest(
    dimacs: bytes,
    *,
    parent_cube: Sequence[int],
    candidate_variables: Sequence[int],
    status_by_path: Mapping[str, str],
    max_depth: int,
    max_nodes: int = DEFAULT_MAX_NODES,
) -> dict[str, Any]:
    """Build a bounded, deterministic, possibly variable-depth cube tree."""

    parsed = parse_dimacs(dimacs)
    parent = _validate_cube(
        parent_cube, parsed["num_variables"], label="parent cube"
    )
    candidates = _candidate_tuple(
        candidate_variables, parsed["num_variables"], parent
    )
    if type(max_depth) is not int or not 0 <= max_depth <= MAX_DEPTH:
        raise AdaptiveCubeError(f"max_depth must be an integer in 0..{MAX_DEPTH}")
    if type(max_nodes) is not int or not 1 <= max_nodes <= MAX_NODE_BUDGET:
        raise AdaptiveCubeError(
            f"max_nodes must be an integer in 1..{MAX_NODE_BUDGET}"
        )
    statuses = _strict_statuses(status_by_path)
    consumed_statuses: set[str] = set()
    nodes_by_id: dict[str, dict[str, Any]] = {}
    local_covers: list[dict[str, Any]] = []
    next_node = 0

    def allocate_node_id(reserved_nodes: int) -> str:
        nonlocal next_node
        if next_node + reserved_nodes >= max_nodes:
            raise AdaptiveCubeError("internal node-budget reservation failed")
        node_id = f"node-{next_node:07d}"
        next_node += 1
        return node_id

    def build_node(
        path: str,
        cube: tuple[int, ...],
        *,
        parent_node_id: str | None,
        parent_cube_sha256: str | None,
        edge_literal: int | None,
        depth: int,
        reserved_nodes: int,
    ) -> str:
        node_id = allocate_node_id(reserved_nodes)
        binding = _cube_binding(parsed, cube)
        bcp = _propagate_parsed(parsed, cube)
        if bcp["conflict"] is True:
            observed_status = BCP_CONFLICT_STATUS
            status_source = "deterministic-bcp-v2"
        elif path in statuses:
            observed_status = statuses[path]
            status_source = "caller-observation-v2"
            consumed_statuses.add(path)
        elif path == "R":
            raise AdaptiveCubeError("missing external status for root path R")
        else:
            observed_status = PENDING_STATUS
            status_source = "generated-frontier-v1"

        ranking: list[dict[str, Any]] = []
        selected_variable: int | None = None
        positive_child_id: str | None = None
        negative_child_id: str | None = None
        terminal_reason: str | None

        if observed_status not in HARD_STATUSES:
            if observed_status == BCP_CONFLICT_STATUS:
                terminal_reason = "BCP_CONFLICT"
            elif observed_status == PENDING_STATUS:
                terminal_reason = "PENDING"
            else:
                terminal_reason = "NON_HARD_STATUS"
        elif depth >= max_depth:
            terminal_reason = "MAX_DEPTH"
        else:
            ranking = _score_parsed(parsed, cube, candidates)
            if not ranking:
                terminal_reason = "NO_UNASSIGNED_CANDIDATE"
            elif max_nodes - next_node < reserved_nodes + 2:
                terminal_reason = "MAX_NODES"
            else:
                terminal_reason = None
                selected_variable = ranking[0]["dimacs_variable"]
                positive_child_id = build_node(
                    path + "+",
                    (*cube, selected_variable),
                    parent_node_id=node_id,
                    parent_cube_sha256=binding["cube_sha256"],
                    edge_literal=selected_variable,
                    depth=depth + 1,
                    reserved_nodes=reserved_nodes + 1,
                )
                negative_child_id = build_node(
                    path + "-",
                    (*cube, -selected_variable),
                    parent_node_id=node_id,
                    parent_cube_sha256=binding["cube_sha256"],
                    edge_literal=-selected_variable,
                    depth=depth + 1,
                    reserved_nodes=reserved_nodes,
                )

        node = seal({
            "node_id": node_id,
            "path": path,
            "depth": depth,
            "parent_node_id": parent_node_id,
            "parent_cube_sha256": parent_cube_sha256,
            "edge_literal": edge_literal,
            "assumptions": list(cube),
            **binding,
            "observed_status": observed_status,
            "status_source": status_source,
            "status_binding_sha256": canonical_sha256({
                "path": path,
                "cube_sha256": binding["cube_sha256"],
                "observed_status": observed_status,
                "status_source": status_source,
            }),
            "bcp": bcp,
            "candidate_ranking": ranking,
            "candidate_ranking_sha256": canonical_sha256(ranking),
            "selected_variable": selected_variable,
            "positive_child_id": positive_child_id,
            "negative_child_id": negative_child_id,
            "terminal_reason": terminal_reason,
        }, "node_sha256")
        nodes_by_id[node_id] = node
        if selected_variable is not None:
            local_covers.append(_cover_record(
                node,
                nodes_by_id[positive_child_id],
                nodes_by_id[negative_child_id],
            ))
        return node_id

    root_id = build_node(
        "R",
        parent,
        parent_node_id=None,
        parent_cube_sha256=None,
        edge_literal=None,
        depth=0,
        reserved_nodes=0,
    )
    unused = sorted(set(statuses) - consumed_statuses)
    if unused:
        raise AdaptiveCubeError(f"external statuses contain unreached paths: {unused}")

    nodes = sorted(nodes_by_id.values(), key=lambda node: _node_number(node["node_id"]))
    covers = sorted(local_covers, key=lambda cover: _node_number(cover["parent_node_id"]))
    tree = seal({
        "root_node_id": root_id,
        "nodes": nodes,
        "local_covers": covers,
        "node_sha256_sequence_sha256": canonical_sha256([
            node["node_sha256"] for node in nodes
        ]),
        "cover_sha256_sequence_sha256": canonical_sha256([
            cover["cover_sha256"] for cover in covers
        ]),
    }, "tree_sha256")
    parent_binding = _cube_binding(parsed, parent)
    return seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": MANIFEST_KIND,
        "cover_formulation": COVER_FORMULATION,
        "authority": AUTHORITY_TEST_ONLY,
        "test_only": True,
        "production_eligible": False,
        "launch_authorized": False,
        "source": {
            "source_cnf_sha256": parsed["source_cnf_sha256"],
            "canonical_cnf_sha256": parsed["canonical_cnf_sha256"],
            "clauses_sha256": parsed["clauses_sha256"],
            "num_variables": parsed["num_variables"],
            "num_clauses": parsed["num_clauses"],
        },
        "parent": {"assumptions": list(parent), **parent_binding},
        "policy": {
            "candidate_variables": list(candidates),
            "candidate_variables_sha256": canonical_sha256(list(candidates)),
            "hard_statuses": sorted(HARD_STATUSES),
            "scoring_formula": SCORING_FORMULA,
            "tie_break": TIE_BREAK,
            "conflict_priority": CONFLICT_PRIORITY,
            "gain_definition": (
                "newly-assigned-variables-after-decision-and-fixed-point-bcp-v2"
            ),
            "gain_includes_decision": True,
            "positive_polarity_is_left": True,
            "scoring_scope": SCORING_SCOPE,
            "max_depth": max_depth,
            "max_nodes": max_nodes,
            "status_input_sha256": canonical_sha256([
                {"path": path, "status": statuses[path]}
                for path in sorted(statuses)
            ]),
        },
        "tree": tree,
        "coverage": _coverage_record(nodes, covers, parent_binding["cube_sha256"]),
        "claim_scope": {
            "solver_invoked": False,
            "terminal_statuses_authenticated_by_solver_proof": False,
            "establishes_only_partition_equivalence": True,
            "production_eligible": False,
            "launch_authorized": False,
        },
    }, "manifest_sha256")


def replay_tree_cover(
    manifest: Mapping[str, Any], dimacs: bytes,
) -> dict[str, Any]:
    """Independently replay tree structure and cover algebra without builder."""

    manifest = _plain_object(manifest, MANIFEST_FIELDS, "adaptive manifest")
    if not selfhash_valid(manifest, "manifest_sha256"):
        raise AdaptiveCubeError("adaptive manifest self-hash mismatch")
    if (
        manifest["schema_version"] != SCHEMA_VERSION
        or manifest["manifest_kind"] != MANIFEST_KIND
        or manifest["cover_formulation"] != COVER_FORMULATION
        or manifest["authority"] != AUTHORITY_TEST_ONLY
        or manifest["test_only"] is not True
        or manifest["production_eligible"] is not False
        or manifest["launch_authorized"] is not False
    ):
        raise AdaptiveCubeError("adaptive manifest TEST_ONLY authority mismatch")

    parsed = parse_dimacs(dimacs)
    source = _plain_object(manifest["source"], SOURCE_FIELDS, "source")
    expected_source = {
        "source_cnf_sha256": parsed["source_cnf_sha256"],
        "canonical_cnf_sha256": parsed["canonical_cnf_sha256"],
        "clauses_sha256": parsed["clauses_sha256"],
        "num_variables": parsed["num_variables"],
        "num_clauses": parsed["num_clauses"],
    }
    if not json_type_equal(source, expected_source):
        raise AdaptiveCubeError("source CNF binding mismatch")

    parent_record = _plain_object(manifest["parent"], PARENT_FIELDS, "parent")
    if type(parent_record["assumptions"]) is not list:
        raise AdaptiveCubeError("parent assumptions must be a JSON list")
    parent = _validate_cube(
        parent_record["assumptions"], parsed["num_variables"], label="parent cube"
    )
    expected_parent = {"assumptions": list(parent), **_cube_binding(parsed, parent)}
    if not json_type_equal(parent_record, expected_parent):
        raise AdaptiveCubeError("parent cube binding mismatch")

    policy = _plain_object(manifest["policy"], POLICY_FIELDS, "policy")
    if type(policy["candidate_variables"]) is not list:
        raise AdaptiveCubeError("policy candidates must be a JSON list")
    candidates = _candidate_tuple(
        policy["candidate_variables"], parsed["num_variables"], parent
    )
    if policy["candidate_variables"] != list(candidates):
        raise AdaptiveCubeError("policy candidates are not canonical")
    if policy["candidate_variables_sha256"] != canonical_sha256(list(candidates)):
        raise AdaptiveCubeError("policy candidate hash mismatch")
    if (
        policy["hard_statuses"] != sorted(HARD_STATUSES)
        or policy["scoring_formula"] != SCORING_FORMULA
        or policy["tie_break"] != TIE_BREAK
        or policy["conflict_priority"] != CONFLICT_PRIORITY
        or policy["gain_definition"]
        != "newly-assigned-variables-after-decision-and-fixed-point-bcp-v2"
        or policy["gain_includes_decision"] is not True
        or policy["positive_polarity_is_left"] is not True
        or policy["scoring_scope"] != SCORING_SCOPE
        or type(policy["max_depth"]) is not int
        or not 0 <= policy["max_depth"] <= MAX_DEPTH
        or type(policy["max_nodes"]) is not int
        or not 1 <= policy["max_nodes"] <= MAX_NODE_BUDGET
    ):
        raise AdaptiveCubeError("adaptive policy mismatch")

    claim_scope = _plain_object(
        manifest["claim_scope"], CLAIM_SCOPE_FIELDS, "claim scope"
    )
    if claim_scope != {
        "solver_invoked": False,
        "terminal_statuses_authenticated_by_solver_proof": False,
        "establishes_only_partition_equivalence": True,
        "production_eligible": False,
        "launch_authorized": False,
    }:
        raise AdaptiveCubeError("claim scope is not TEST_ONLY")

    tree = _plain_object(manifest["tree"], TREE_FIELDS, "tree")
    if type(tree["nodes"]) is not list or type(tree["local_covers"]) is not list:
        raise AdaptiveCubeError("tree nodes and covers must be JSON lists")
    if not selfhash_valid(tree, "tree_sha256"):
        raise AdaptiveCubeError("tree self-hash mismatch")
    if not 1 <= len(tree["nodes"]) <= policy["max_nodes"]:
        raise AdaptiveCubeError("tree node count violates max_nodes")

    nodes_by_id: dict[str, dict[str, Any]] = {}
    ordered_ids: list[str] = []
    external_statuses: dict[str, str] = {}
    for raw_node in tree["nodes"]:
        node = _plain_object(raw_node, NODE_FIELDS, "tree node")
        node_id = node["node_id"]
        _node_number(node_id)
        if node_id in nodes_by_id:
            raise AdaptiveCubeError("tree contains duplicate node id")
        if not selfhash_valid(node, "node_sha256"):
            raise AdaptiveCubeError("tree node self-hash mismatch")
        if type(node["assumptions"]) is not list:
            raise AdaptiveCubeError("node assumptions must be a JSON list")
        cube = _validate_cube(
            node["assumptions"], parsed["num_variables"], label="node assumptions"
        )
        binding = _cube_binding(parsed, cube)
        if any(node[key] != binding[key] for key in binding):
            raise AdaptiveCubeError("node cube or CNF binding mismatch")
        bcp = _plain_object(node["bcp"], BCP_FIELDS, "node BCP")
        if not selfhash_valid(bcp, "bcp_sha256"):
            raise AdaptiveCubeError("node BCP self-hash mismatch")
        expected_bcp = _propagate_parsed(parsed, cube)
        if not json_type_equal(bcp, expected_bcp):
            raise AdaptiveCubeError("node BCP differs from fresh replay")
        expected_status_hash = canonical_sha256({
            "path": node["path"],
            "cube_sha256": node["cube_sha256"],
            "observed_status": node["observed_status"],
            "status_source": node["status_source"],
        })
        if node["status_binding_sha256"] != expected_status_hash:
            raise AdaptiveCubeError("node status binding mismatch")
        if type(node["candidate_ranking"]) is not list:
            raise AdaptiveCubeError("candidate ranking must be a JSON list")
        if node["candidate_ranking_sha256"] != canonical_sha256(
            node["candidate_ranking"]
        ):
            raise AdaptiveCubeError("candidate ranking hash mismatch")
        for record in node["candidate_ranking"]:
            _plain_object(record, RANKING_FIELDS, "candidate ranking record")
        if node["status_source"] == "caller-observation-v2":
            if (
                node["observed_status"] not in EXTERNAL_STATUSES
                or type(node["path"]) is not str
                or node["path"] in external_statuses
            ):
                raise AdaptiveCubeError("caller status record is malformed")
            external_statuses[node["path"]] = node["observed_status"]
        nodes_by_id[node_id] = node
        ordered_ids.append(node_id)

    if ordered_ids != sorted(ordered_ids, key=_node_number):
        raise AdaptiveCubeError("tree node order is not canonical")
    if tree["node_sha256_sequence_sha256"] != canonical_sha256([
        nodes_by_id[node_id]["node_sha256"] for node_id in ordered_ids
    ]):
        raise AdaptiveCubeError("tree node hash sequence mismatch")
    if policy["status_input_sha256"] != canonical_sha256([
        {"path": path, "status": external_statuses[path]}
        for path in sorted(external_statuses)
    ]):
        raise AdaptiveCubeError("external status input hash mismatch")

    root_id = tree["root_node_id"]
    if type(root_id) is not str or root_id not in nodes_by_id:
        raise AdaptiveCubeError("tree root is missing")
    if sum(node["parent_node_id"] is None for node in nodes_by_id.values()) != 1:
        raise AdaptiveCubeError("tree does not have a unique root")

    visiting: set[str] = set()
    visited: set[str] = set()
    internal_nodes: list[dict[str, Any]] = []
    terminal_nodes: list[dict[str, Any]] = []

    def walk(
        node_id: str,
        *,
        expected_parent_id: str | None,
        expected_parent_cube_sha256: str | None,
        expected_path: str,
        expected_depth: int,
        expected_edge_literal: int | None,
        expected_assumptions: tuple[int, ...],
    ) -> None:
        if node_id in visiting:
            raise AdaptiveCubeError("tree contains a cycle")
        if node_id in visited:
            raise AdaptiveCubeError("tree contains a shared child")
        if node_id not in nodes_by_id:
            raise AdaptiveCubeError("tree references a missing child")
        visiting.add(node_id)
        node = nodes_by_id[node_id]
        if (
            node["parent_node_id"] != expected_parent_id
            or node["parent_cube_sha256"] != expected_parent_cube_sha256
            or node["path"] != expected_path
            or type(node["depth"]) is not int
            or node["depth"] != expected_depth
            or node["edge_literal"] != expected_edge_literal
            or not json_type_equal(node["assumptions"], list(expected_assumptions))
        ):
            raise AdaptiveCubeError("tree edge, path, or assumptions mismatch")

        bcp_conflict = node["bcp"]["conflict"] is True
        source = node["status_source"]
        status = node["observed_status"]
        reason = node["terminal_reason"]
        if bcp_conflict:
            if (
                status != BCP_CONFLICT_STATUS
                or source != "deterministic-bcp-v2"
                or reason != "BCP_CONFLICT"
            ):
                raise AdaptiveCubeError("BCP conflict status truth table mismatch")
        elif source == "generated-frontier-v1":
            if status != PENDING_STATUS or reason != "PENDING":
                raise AdaptiveCubeError("PENDING frontier truth table mismatch")
        elif source == "caller-observation-v2":
            if status not in EXTERNAL_STATUSES:
                raise AdaptiveCubeError("caller status is invalid")
        else:
            raise AdaptiveCubeError("node status source is invalid")

        expected_ranking: list[dict[str, Any]] = []
        if (
            not bcp_conflict
            and source == "caller-observation-v2"
            and status in HARD_STATUSES
            and expected_depth < policy["max_depth"]
        ):
            expected_ranking = _score_parsed(parsed, expected_assumptions, candidates)
        if not json_type_equal(node["candidate_ranking"], expected_ranking):
            raise AdaptiveCubeError("candidate ranking differs from fresh replay")

        if reason is None:
            if (
                source != "caller-observation-v2"
                or status not in HARD_STATUSES
                or not expected_ranking
                or node["selected_variable"]
                != expected_ranking[0]["dimacs_variable"]
                or type(node["positive_child_id"]) is not str
                or type(node["negative_child_id"]) is not str
                or node["positive_child_id"] == node["negative_child_id"]
            ):
                raise AdaptiveCubeError("internal node split policy mismatch")
            internal_nodes.append(node)
            variable = node["selected_variable"]
            walk(
                node["positive_child_id"],
                expected_parent_id=node_id,
                expected_parent_cube_sha256=node["cube_sha256"],
                expected_path=expected_path + "+",
                expected_depth=expected_depth + 1,
                expected_edge_literal=variable,
                expected_assumptions=(*expected_assumptions, variable),
            )
            walk(
                node["negative_child_id"],
                expected_parent_id=node_id,
                expected_parent_cube_sha256=node["cube_sha256"],
                expected_path=expected_path + "-",
                expected_depth=expected_depth + 1,
                expected_edge_literal=-variable,
                expected_assumptions=(*expected_assumptions, -variable),
            )
        else:
            if any(node[key] is not None for key in (
                "selected_variable", "positive_child_id", "negative_child_id",
            )):
                raise AdaptiveCubeError("terminal node has split children")
            if not bcp_conflict and source == "caller-observation-v2":
                if status in NON_HARD_STATUSES and reason != "NON_HARD_STATUS":
                    raise AdaptiveCubeError("non-hard terminal reason mismatch")
                if status in HARD_STATUSES:
                    if expected_depth >= policy["max_depth"]:
                        expected_reason = "MAX_DEPTH"
                    elif not expected_ranking:
                        expected_reason = "NO_UNASSIGNED_CANDIDATE"
                    else:
                        expected_reason = "MAX_NODES"
                    if reason != expected_reason:
                        raise AdaptiveCubeError("hard terminal reason mismatch")
            terminal_nodes.append(node)
        visiting.remove(node_id)
        visited.add(node_id)

    walk(
        root_id,
        expected_parent_id=None,
        expected_parent_cube_sha256=None,
        expected_path="R",
        expected_depth=0,
        expected_edge_literal=None,
        expected_assumptions=parent,
    )
    if visited != set(nodes_by_id):
        raise AdaptiveCubeError("tree contains orphan nodes")
    terminal_paths = [node["path"] for node in terminal_nodes]
    for left in terminal_paths:
        for right in terminal_paths:
            if left != right and right.startswith(left):
                raise AdaptiveCubeError("terminal paths are not prefix-free")

    stored_covers = tree["local_covers"]
    for cover in stored_covers:
        cover = _plain_object(cover, COVER_FIELDS, "local cover")
        _plain_object(cover["positive_child"], COVER_CHILD_FIELDS, "positive cover child")
        _plain_object(cover["negative_child"], COVER_CHILD_FIELDS, "negative cover child")
        if not selfhash_valid(cover, "cover_sha256"):
            raise AdaptiveCubeError("local cover self-hash mismatch")
    expected_covers = sorted([
        _cover_record(
            node,
            nodes_by_id[node["positive_child_id"]],
            nodes_by_id[node["negative_child_id"]],
        )
        for node in internal_nodes
    ], key=lambda cover: _node_number(cover["parent_node_id"]))
    if not json_type_equal(stored_covers, expected_covers):
        raise AdaptiveCubeError("local covers differ from independent replay")
    if tree["cover_sha256_sequence_sha256"] != canonical_sha256([
        cover["cover_sha256"] for cover in stored_covers
    ]):
        raise AdaptiveCubeError("tree cover hash sequence mismatch")

    coverage = _plain_object(manifest["coverage"], COVERAGE_FIELDS, "coverage")
    expected_coverage = _coverage_record(
        tree["nodes"], stored_covers, parent_record["cube_sha256"]
    )
    if not json_type_equal(coverage, expected_coverage):
        raise AdaptiveCubeError("coverage differs from independent replay")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "record_kind": "paper400-dic5-adaptive-tree-cover-replay-v2",
        "valid": True,
        "manifest_sha256": manifest["manifest_sha256"],
        "tree_sha256": tree["tree_sha256"],
        "node_count": len(nodes_by_id),
        "internal_node_count": len(internal_nodes),
        "terminal_leaf_count": len(terminal_nodes),
        "mutually_exclusive": True,
        "exhaustive": True,
        "solver_invoked": False,
        "launch_authorized": False,
    }, "record_sha256")


def verify_adaptive_manifest(
    manifest: Mapping[str, Any],
    dimacs: bytes,
    *,
    expected_manifest_sha256: str | None = None,
) -> dict[str, Any]:
    """Run independent cover replay plus type-exact deterministic rebuild."""

    manifest = _plain_object(manifest, MANIFEST_FIELDS, "adaptive manifest")
    if not selfhash_valid(manifest, "manifest_sha256"):
        raise AdaptiveCubeError("adaptive manifest self-hash mismatch")
    stored_hash = manifest["manifest_sha256"]
    authenticated = expected_manifest_sha256 is not None
    if authenticated:
        if not _is_sha256(expected_manifest_sha256):
            raise AdaptiveCubeError("expected manifest SHA-256 is malformed")
        if stored_hash != expected_manifest_sha256:
            raise AdaptiveCubeError("adaptive manifest does not match pinned SHA-256")

    tree_replay = replay_tree_cover(manifest, dimacs)
    parent = manifest["parent"]
    policy = manifest["policy"]
    statuses: dict[str, str] = {}
    for node in manifest["tree"]["nodes"]:
        if node["status_source"] == "caller-observation-v2":
            path = node["path"]
            if path in statuses:
                raise AdaptiveCubeError("external status path is duplicate")
            statuses[path] = node["observed_status"]
    try:
        rebuilt = build_adaptive_manifest(
            dimacs,
            parent_cube=parent["assumptions"],
            candidate_variables=policy["candidate_variables"],
            status_by_path=statuses,
            max_depth=policy["max_depth"],
            max_nodes=policy["max_nodes"],
        )
    except (KeyError, TypeError) as exc:
        raise AdaptiveCubeError("adaptive manifest replay inputs are malformed") from exc
    if not json_type_equal(rebuilt, manifest):
        raise AdaptiveCubeError(
            "adaptive manifest differs in value or JSON type from fresh exact replay"
        )
    parsed = parse_dimacs(dimacs)
    return seal({
        "schema_version": SCHEMA_VERSION,
        "record_kind": "paper400-dic5-adaptive-lookahead-verification-v2",
        "valid": True,
        "authenticated": authenticated,
        "test_only": True,
        "production_eligible": False,
        "launch_authorized": False,
        "manifest_sha256": stored_hash,
        "source_cnf_sha256": parsed["source_cnf_sha256"],
        "tree_replay_record_sha256": tree_replay["record_sha256"],
        "mutually_exclusive": True,
        "exhaustive": True,
        "terminal_leaf_count": rebuilt["coverage"]["terminal_leaf_count"],
    }, "record_sha256")


__all__ = [
    "AUTHORITY_TEST_ONLY",
    "AdaptiveCubeError",
    "BCP_CONFLICT_STATUS",
    "CONFLICT_PRIORITY",
    "COVER_FORMULATION",
    "DEFAULT_MAX_NODES",
    "EXTERNAL_STATUSES",
    "HARD_STATUSES",
    "MANIFEST_KIND",
    "MAX_DEPTH",
    "MAX_NODE_BUDGET",
    "PENDING_STATUS",
    "SCHEMA_VERSION",
    "SCORING_FORMULA",
    "SCORING_SCOPE",
    "TIE_BREAK",
    "build_adaptive_manifest",
    "canonical_bytes",
    "canonical_sha256",
    "deterministic_bcp",
    "json_type_equal",
    "parse_dimacs",
    "render_cube_dimacs",
    "replay_tree_cover",
    "score_candidates",
    "seal",
    "selfhash_valid",
    "verify_adaptive_manifest",
]
