"""Deterministic, answer-free semantic DAGs for native blind targets.

This module deliberately does not try to solve a problem or infer chemistry.
It turns the already validated problem-side evidence into a small dependency
skeleton that makes two obligations explicit:

* prior subparts are inputs that still have to be derived in the blind run;
* every requested output must be connected to the bound source facts.

The controller builds the object, hashes its canonical JSON representation,
and gives only that immutable skeleton to solver/reviewer prompts.  No runtime
model output is accepted as DAG state.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from typing import Any


SEMANTIC_DAG_SCHEMA_VERSION = 2
SEMANTIC_DAG_AUTHORITY = "controller"

_ALLOWED_AUDIT_REQUIREMENTS = {"image_component_accounting"}
_ALLOWED_EDGE_KINDS = {
    "connection_support",
    "discharges",
    "inventory_support",
    "output_dependency",
    "source_support",
    "stoichiometric_support",
}
_SEMANTIC_DAG_FIELDS = {
    "schema_version",
    "authority",
    "evaluation_mode",
    "record_id",
    "nodes",
    "edges",
}
_SOURCE_IMAGE_NODE_FIELDS = {"id", "kind", "path", "sha256"}
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class SemanticDagError(ValueError):
    """Raised when source evidence cannot produce a safe semantic DAG."""


def _canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def _sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _normalized_key(raw: Any) -> str:
    key = str(raw)
    snake = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", key)
    return re.sub(r"[^a-z0-9]+", "_", snake.lower()).strip("_")


def _answer_bearing_paths(value: Any, *, path: str = "evidence") -> list[str]:
    """Return forbidden source keys, independent of their payload value."""
    found: list[str] = []
    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            normalized = _normalized_key(raw_key)
            parts = tuple(part for part in normalized.split("_") if part)
            child_path = f"{path}.{raw_key}"
            if (
                normalized == "result_spec"
                or normalized.startswith("official_")
                or normalized == "reusable_conclusions"
                or any(
                    part in {
                        "answer",
                        "answers",
                        "explanation",
                        "grader",
                        "grading",
                        "marking",
                        "reasoning",
                        "rubric",
                        "solution",
                        "solutions",
                    }
                    for part in parts
                )
            ):
                found.append(child_path)
            found.extend(_answer_bearing_paths(child, path=child_path))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            found.extend(
                _answer_bearing_paths(child, path=f"{path}[{index}]")
            )
    return found


def _nonempty_string(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise SemanticDagError(f"{label} must be a non-empty string")
    return value.strip()


def _optional_string(value: Any, *, label: str) -> str:
    if value is None:
        return ""
    if not isinstance(value, str):
        raise SemanticDagError(f"{label} must be a string")
    return value.strip()


def _previous_part_node(raw: Any, index: int) -> dict[str, Any]:
    if not isinstance(raw, Mapping):
        raise SemanticDagError(f"previous_parts[{index}] must be an object")
    forbidden = _answer_bearing_paths(raw, path=f"previous_parts[{index}]")
    if forbidden:
        raise SemanticDagError(
            "previous part contains answer-bearing field(s): "
            + ", ".join(forbidden)
        )
    source_id = _nonempty_string(
        raw.get("source_id"), label=f"previous_parts[{index}].source_id"
    )
    question = _nonempty_string(
        raw.get("question"), label=f"previous_parts[{index}].question"
    )
    return {
        "id": f"previous:{index}",
        "kind": "previous_part_prerequisite",
        "source_id": source_id,
        "part_id": _optional_string(
            raw.get("part_id"), label=f"previous_parts[{index}].part_id"
        ),
        "question": question,
        "question_sha256": _sha256(question),
        "dependency_policy": _optional_string(
            raw.get("dependency_policy"),
            label=f"previous_parts[{index}].dependency_policy",
        ),
        "state": "requires_blind_derivation",
    }


def _source_image_node(raw: Any, index: int) -> dict[str, Any]:
    if not isinstance(raw, Mapping) or set(raw) != {"path", "sha256"}:
        raise SemanticDagError(
            f"source_images[{index}] must contain exactly path and sha256"
        )
    path = _nonempty_string(
        raw.get("path"), label=f"source_images[{index}].path"
    )
    digest = _nonempty_string(
        raw.get("sha256"), label=f"source_images[{index}].sha256"
    )
    if not _SHA256_RE.fullmatch(digest):
        raise SemanticDagError(
            f"source_images[{index}].sha256 must be a lowercase SHA-256 digest"
        )
    return {
        "id": f"source_image:{index}",
        "kind": "source_image",
        "path": path,
        "sha256": digest,
    }


def _requested_output_nodes(
    raw: Any, index: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    if not isinstance(raw, Mapping):
        raise SemanticDagError(f"requested_outputs[{index}] must be an object")
    forbidden = _answer_bearing_paths(raw, path=f"requested_outputs[{index}]")
    if forbidden:
        raise SemanticDagError(
            "requested output contains answer-bearing field(s): "
            + ", ".join(forbidden)
        )
    output_id = _nonempty_string(
        raw.get("id"), label=f"requested_outputs[{index}].id"
    )
    requirement = _nonempty_string(
        raw.get("source_requirement"),
        label=f"requested_outputs[{index}].source_requirement",
    )
    value_kind = _nonempty_string(
        raw.get("kind"), label=f"requested_outputs[{index}].kind"
    )
    audit_requirements = raw.get("audit_requirements", [])
    if (
        not isinstance(audit_requirements, list)
        or ("audit_requirements" in raw and not audit_requirements)
        or not all(
            isinstance(item, str) for item in audit_requirements
        )
        or len(set(audit_requirements)) != len(audit_requirements)
        or any(
            item not in _ALLOWED_AUDIT_REQUIREMENTS
            for item in audit_requirements
        )
    ):
        raise SemanticDagError(
            f"requested_outputs[{index}].audit_requirements is invalid"
        )
    policy = raw.get("reporting_policy", {})
    if not isinstance(policy, Mapping):
        raise SemanticDagError(
            f"requested_outputs[{index}].reporting_policy must be an object"
        )
    policy = dict(policy)
    derive = {
        "id": f"derive:{output_id}",
        "kind": "derivation_obligation",
        "output_id": output_id,
        "source_requirement": requirement,
        "state": "open",
    }
    output = {
        "id": f"output:{output_id}",
        "kind": "requested_output",
        "output_id": output_id,
        "value_kind": value_kind,
        "source_requirement": requirement,
        "unit": _optional_string(
            raw.get("unit"), label=f"requested_outputs[{index}].unit"
        ),
        "reporting_policy": policy,
        "state": "unresolved",
    }
    if audit_requirements:
        output["audit_requirements"] = list(audit_requirements)
    dependencies = raw.get("depends_on_output_ids", [])
    if (
        not isinstance(dependencies, list)
        or ("depends_on_output_ids" in raw and not dependencies)
        or not all(
            isinstance(dependency, str) and dependency.strip()
            for dependency in dependencies
        )
    ):
        raise SemanticDagError(
            f"requested_outputs[{index}].depends_on_output_ids is invalid"
        )
    dependencies = [dependency.strip() for dependency in dependencies]
    if len(set(dependencies)) != len(dependencies):
        raise SemanticDagError(
            f"requested_outputs[{index}].depends_on_output_ids is invalid"
        )
    if dependencies:
        output["depends_on_output_ids"] = dependencies
    return derive, output


def _validate_output_dependencies(outputs: list[dict[str, Any]]) -> None:
    positions = {
        output["output_id"]: index for index, output in enumerate(outputs)
    }
    dependencies_by_id: dict[str, list[str]] = {}
    for index, output in enumerate(outputs):
        output_id = output["output_id"]
        dependencies = output.get("depends_on_output_ids", [])
        for dependency in dependencies:
            if dependency not in positions:
                raise SemanticDagError(
                    f"requested_outputs[{index}].depends_on_output_ids "
                    f"references unknown output id {dependency!r}"
                )
            if dependency == output_id:
                raise SemanticDagError(
                    f"requested_outputs[{index}].depends_on_output_ids "
                    "contains a self dependency"
                )
        dependencies_by_id[output_id] = list(dependencies)

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(output_id: str) -> None:
        if output_id in visiting:
            raise SemanticDagError(
                "requested_outputs.depends_on_output_ids contains a cycle"
            )
        if output_id in visited:
            return
        visiting.add(output_id)
        for dependency in dependencies_by_id[output_id]:
            visit(dependency)
        visiting.remove(output_id)
        visited.add(output_id)

    for output_id in dependencies_by_id:
        visit(output_id)

    for index, output in enumerate(outputs):
        for dependency in output.get("depends_on_output_ids", []):
            if positions[dependency] >= index:
                raise SemanticDagError(
                    f"requested_outputs[{index}].depends_on_output_ids must "
                    "reference only earlier requested outputs"
                )


def build_semantic_dag(
    *,
    record_id: str,
    problem_evidence: Mapping[str, Any],
    source_images: list[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Build a deterministic DAG from validated problem-only evidence.

    Text-bearing source nodes store only field hashes because the same text is
    already present once in the native source contract.  Prior-part questions
    and requested-output requirements are retained because they are the labels
    a solver needs to navigate the dependency skeleton.
    """
    record_id = _nonempty_string(record_id, label="record_id")
    if not isinstance(problem_evidence, Mapping):
        raise SemanticDagError("problem_evidence must be an object")
    forbidden = _answer_bearing_paths(problem_evidence)
    if forbidden:
        raise SemanticDagError(
            "problem evidence contains answer-bearing field(s): "
            + ", ".join(forbidden)
        )

    nodes: list[dict[str, Any]] = []
    input_ids: list[str] = []
    for field in ("question", "shared_context", "current_question"):
        text = _optional_string(
            problem_evidence.get(field), label=f"problem_evidence.{field}"
        )
        if not text:
            if field in {"question", "current_question"}:
                raise SemanticDagError(
                    f"problem_evidence.{field} must be a non-empty string"
                )
            continue
        node_id = f"source:{field}"
        nodes.append({
            "id": node_id,
            "kind": "source_fact_set",
            "source_field": field,
            "sha256": _sha256(text),
        })
        input_ids.append(node_id)

    previous = problem_evidence.get("previous_parts")
    if not isinstance(previous, list):
        raise SemanticDagError("problem_evidence.previous_parts must be a list")
    previous_source_ids: set[str] = set()
    for index, raw in enumerate(previous):
        node = _previous_part_node(raw, index)
        if node["source_id"] in previous_source_ids:
            raise SemanticDagError("previous_parts contains duplicate source_id")
        previous_source_ids.add(node["source_id"])
        nodes.append(node)
        input_ids.append(node["id"])

    raw_source_images = [] if source_images is None else source_images
    if not isinstance(raw_source_images, list):
        raise SemanticDagError("source_images must be a list")
    source_image_paths: set[str] = set()
    for index, raw in enumerate(raw_source_images):
        node = _source_image_node(raw, index)
        if node["path"] in source_image_paths:
            raise SemanticDagError("source_images contains a duplicate path")
        source_image_paths.add(node["path"])
        nodes.append(node)
        input_ids.append(node["id"])

    requested = problem_evidence.get("requested_outputs")
    if not isinstance(requested, list) or not requested:
        raise SemanticDagError(
            "problem_evidence.requested_outputs must be a non-empty list"
        )
    output_ids: set[str] = set()
    derivations: list[dict[str, Any]] = []
    outputs: list[dict[str, Any]] = []
    for index, raw in enumerate(requested):
        derive, output = _requested_output_nodes(raw, index)
        if output["output_id"] in output_ids:
            raise SemanticDagError("requested_outputs contains duplicate id")
        output_ids.add(output["output_id"])
        derivations.append(derive)
        outputs.append(output)
    _validate_output_dependencies(outputs)

    audit_nodes_by_output: dict[str, tuple[str, str, str]] = {}
    for output in outputs:
        requirements = output.get("audit_requirements", [])
        if "image_component_accounting" not in requirements:
            continue
        if not raw_source_images:
            raise SemanticDagError(
                "image_component_accounting requires at least one source image"
            )
        output_id = output["output_id"]
        inventory_id = f"component_inventory:{output_id}"
        graph_id = f"connection_graph:{output_id}"
        balance_id = f"stoichiometric_balance:{output_id}"
        nodes.extend([
            {
                "id": inventory_id,
                "kind": "component_inventory",
                "output_id": output_id,
                "state": "open",
            },
            {
                "id": graph_id,
                "kind": "connection_graph",
                "output_id": output_id,
                "state": "open",
            },
            {
                "id": balance_id,
                "kind": "stoichiometric_balance",
                "output_id": output_id,
                "state": "open",
            },
        ])
        audit_nodes_by_output[output_id] = (
            inventory_id, graph_id, balance_id,
        )
    nodes.extend(derivations)
    nodes.extend(outputs)

    outputs_by_id = {output["output_id"]: output for output in outputs}
    edges: list[dict[str, str]] = []
    for derive in derivations:
        audit_nodes = audit_nodes_by_output.get(derive["output_id"])
        source_target = audit_nodes[0] if audit_nodes else derive["id"]
        for source_id in input_ids:
            edges.append({
                "from": source_id,
                "to": source_target,
                "kind": "source_support",
            })
        if audit_nodes:
            inventory_id, graph_id, balance_id = audit_nodes
            edges.extend([
                {
                    "from": inventory_id,
                    "to": graph_id,
                    "kind": "inventory_support",
                },
                {
                    "from": graph_id,
                    "to": balance_id,
                    "kind": "connection_support",
                },
                {
                    "from": balance_id,
                    "to": derive["id"],
                    "kind": "stoichiometric_support",
                },
            ])
        output = outputs_by_id[derive["output_id"]]
        for dependency in output.get("depends_on_output_ids", []):
            edges.append({
                "from": f"output:{dependency}",
                "to": derive["id"],
                "kind": "output_dependency",
            })
        edges.append({
            "from": derive["id"],
            "to": f"output:{derive['output_id']}",
            "kind": "discharges",
        })

    return {
        "schema_version": SEMANTIC_DAG_SCHEMA_VERSION,
        "authority": SEMANTIC_DAG_AUTHORITY,
        "evaluation_mode": "answer_blind",
        "record_id": record_id,
        "nodes": nodes,
        "edges": edges,
    }


def semantic_dag_provenance(dag: Mapping[str, Any]) -> dict[str, Any]:
    """Validate the complete graph and return its controller-owned summary."""
    if not isinstance(dag, Mapping):
        raise SemanticDagError("semantic DAG must be an object")
    forbidden = _answer_bearing_paths(dag, path="semantic_dag")
    if forbidden:
        raise SemanticDagError(
            "semantic DAG contains answer-bearing field(s): "
            + ", ".join(forbidden)
        )
    if set(dag) != _SEMANTIC_DAG_FIELDS:
        raise SemanticDagError("semantic DAG header fields are invalid")
    nodes = dag.get("nodes")
    edges = dag.get("edges")
    if (
        dag.get("schema_version") != SEMANTIC_DAG_SCHEMA_VERSION
        or dag.get("authority") != SEMANTIC_DAG_AUTHORITY
        or dag.get("evaluation_mode") != "answer_blind"
        or not isinstance(nodes, list)
        or not isinstance(edges, list)
    ):
        raise SemanticDagError("semantic DAG header is invalid")
    _nonempty_string(dag.get("record_id"), label="semantic DAG record_id")

    kinds: dict[str, int] = {}
    output_ids: list[str] = []
    output_id_set: set[str] = set()
    previous_source_ids: list[str] = []
    node_ids: set[str] = set()
    source_image_paths: set[str] = set()
    for index, node in enumerate(nodes):
        if not isinstance(node, Mapping):
            raise SemanticDagError(
                f"semantic DAG node {index} is not an object"
            )
        node_id = _nonempty_string(
            node.get("id"), label=f"semantic DAG node {index} id"
        )
        if node_id in node_ids:
            raise SemanticDagError("semantic DAG contains a duplicate node id")
        node_ids.add(node_id)
        kind = _nonempty_string(
            node.get("kind"), label=f"semantic DAG node {index} kind"
        )
        kinds[kind] = kinds.get(kind, 0) + 1
        if kind == "requested_output":
            output_id = _nonempty_string(
                node.get("output_id"), label="semantic DAG output_id"
            )
            if output_id in output_id_set:
                raise SemanticDagError(
                    "semantic DAG contains a duplicate requested output id"
                )
            output_id_set.add(output_id)
            output_ids.append(output_id)
        elif kind == "previous_part_prerequisite":
            previous_source_ids.append(
                _nonempty_string(
                    node.get("source_id"),
                    label="semantic DAG previous source_id",
                )
            )
        elif kind == "source_image":
            if set(node) != _SOURCE_IMAGE_NODE_FIELDS:
                raise SemanticDagError(
                    "semantic DAG source_image fields are invalid"
                )
            path = _nonempty_string(
                node.get("path"), label="semantic DAG source_image path"
            )
            digest = _nonempty_string(
                node.get("sha256"), label="semantic DAG source_image sha256"
            )
            if not _SHA256_RE.fullmatch(digest):
                raise SemanticDagError(
                    "semantic DAG source_image sha256 is invalid"
                )
            if path in source_image_paths:
                raise SemanticDagError(
                    "semantic DAG contains a duplicate source_image path"
                )
            source_image_paths.add(path)

    adjacency: dict[str, list[str]] = {
        node_id: [] for node_id in node_ids
    }
    indegree = {node_id: 0 for node_id in node_ids}
    seen_edges: set[tuple[str, str, str]] = set()
    seen_directed_pairs: set[tuple[str, str]] = set()
    for index, edge in enumerate(edges):
        if not isinstance(edge, Mapping) or set(edge) != {"from", "to", "kind"}:
            raise SemanticDagError(
                f"semantic DAG edge {index} fields are invalid"
            )
        source = _nonempty_string(
            edge.get("from"), label=f"semantic DAG edge {index} from"
        )
        target = _nonempty_string(
            edge.get("to"), label=f"semantic DAG edge {index} to"
        )
        kind = _nonempty_string(
            edge.get("kind"), label=f"semantic DAG edge {index} kind"
        )
        if kind not in _ALLOWED_EDGE_KINDS:
            raise SemanticDagError(
                f"semantic DAG edge {index} kind is invalid"
            )
        if source not in node_ids or target not in node_ids:
            raise SemanticDagError(
                f"semantic DAG edge {index} has a dangling endpoint"
            )
        if source == target:
            raise SemanticDagError(
                f"semantic DAG edge {index} is a self edge"
            )
        triple = (source, target, kind)
        if triple in seen_edges:
            raise SemanticDagError("semantic DAG contains a duplicate edge")
        seen_edges.add(triple)
        directed_pair = (source, target)
        if directed_pair in seen_directed_pairs:
            raise SemanticDagError(
                "semantic DAG contains a duplicate directed edge"
            )
        seen_directed_pairs.add(directed_pair)
        adjacency[source].append(target)
        indegree[target] += 1

    queue = [
        node_id for node_id in node_ids if indegree[node_id] == 0
    ]
    visited_count = 0
    queue_index = 0
    while queue_index < len(queue):
        source = queue[queue_index]
        queue_index += 1
        visited_count += 1
        for target in adjacency[source]:
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    if visited_count != len(node_ids):
        raise SemanticDagError("semantic DAG contains a directed cycle")

    return {
        "schema_version": SEMANTIC_DAG_SCHEMA_VERSION,
        "authority": SEMANTIC_DAG_AUTHORITY,
        "sha256": _sha256(dict(dag)),
        "node_count": len(nodes),
        "edge_count": len(edges),
        "node_kind_counts": dict(sorted(kinds.items())),
        "requested_output_ids": output_ids,
        "previous_part_source_ids": previous_source_ids,
    }


def render_solver_semantic_dag_prompt(
    dag: Mapping[str, Any],
    provenance: Mapping[str, Any] | None = None,
) -> str:
    """Render the immutable skeleton for a Formalizer or native Reviewer."""
    bound = semantic_dag_provenance(dag)
    if provenance is not None and dict(provenance) != bound:
        raise SemanticDagError("semantic DAG provenance is stale or mismatched")
    return (
        "CONTROLLER SEMANTIC DAG (immutable, no solved values):\n"
        "- Provenance: "
        + json.dumps(bound, ensure_ascii=False, sort_keys=True)
        + "\n- Skeleton: "
        + json.dumps(dict(dag), ensure_ascii=False, sort_keys=True)
        + "\nTreat source_fact_set nodes as references to the inline bound problem "
        "evidence. Derive every previous_part_prerequisite inside the blind "
        "run (or use only its declared fallback policy), discharge every "
        "derivation_obligation, and expose one Lean carrier for every "
        "requested_output. The states open, requires_blind_derivation, and "
        "unresolved are obligations, never source conclusions. Follow every "
        "output_dependency edge in order: derive its antecedent output first "
        "and use that exact derived carrier in the dependent derivation. For "
        "each requested_output whose immutable audit_requirements contains "
        "image_component_accounting, inspect every source_image node before "
        "doing arithmetic. On the first draft, complete the semantic chain in "
        "this order: (1) component_inventory records every visually distinct "
        "building-block identity and formula; (2) connection_graph records "
        "connection degree, functional-group ports, their LCM/multiplicity "
        "match, and a connected whole-product topology across repeated units, "
        "terminal fragments, caps/adducts, and every bracket/connector/cross-"
        "boundary bond and the preceding-page unit pattern; (3) "
        "stoichiometric_balance records the number and type of connections, "
        "the exact count of eliminated small molecules, and the unreduced "
        "whole-product formula or quantity; (4) record the GCD or other "
        "normalization. Only after this component ledger is complete may the "
        "derivation_obligation be discharged and the requested output "
        "calculated. A printed formula can be a residue "
        "rather than the whole product. Every source_image path/digest is "
        "controller-bound evidence, not a solved value. "
        "This opt-in obligation is mandatory and cannot be marked "
        "not_applicable.\n"
    )
