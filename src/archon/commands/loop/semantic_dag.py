"""Deterministic, answer-free semantic DAGs for native blind targets.

This module deliberately does not try to solve a problem or infer chemistry.
It turns the already validated problem-side evidence into a small dependency
skeleton that makes two obligations explicit:

* source-referenced prior subparts are inputs that still have to be derived in
  the blind run;
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


SEMANTIC_DAG_SCHEMA_VERSION = 1
SEMANTIC_DAG_AUTHORITY = "controller"

_ALLOWED_AUDIT_REQUIREMENTS = {"image_component_accounting"}


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


def _mentions_previous_part(text: str, node: Mapping[str, Any]) -> bool:
    """Return whether task text explicitly names one previous-part node."""
    folded = text.casefold()
    for field in ("source_id", "part_id"):
        identifier = str(node.get(field) or "").strip().casefold()
        if identifier and re.search(
            rf"(?<![A-Za-z0-9]){re.escape(identifier)}"
            r"(?![A-Za-z0-9])",
            folded,
        ):
            return True

    # Olympiad statements commonly cite T4-A4 as "4.4".  Require a direct
    # result cue so an unrelated decimal or a reference to source fragments is
    # not treated as narrowing the declared prior-part data flow.
    part_id = str(node.get("part_id") or "")
    numbers = re.findall(r"[A-Za-z]*([0-9]+)", part_id)
    if len(numbers) < 2:
        return False
    dotted = re.compile(
        rf"(?<![0-9.]){re.escape(numbers[-2])}\s*\.\s*"
        rf"{re.escape(numbers[-1])}(?![0-9.])"
    )
    for match in dotted.finditer(text):
        prefix = text[max(0, match.start() - 48):match.start()]
        if re.search(
            r"\b(?:answer|result|value)\b"
            r"[^.\n!?;:]{0,32}\b(?:for|from|in|of|to)\b"
            r"(?:\s+(?:part|question|subquestion))?\s*$",
            prefix,
            flags=re.IGNORECASE,
        ):
            return True
    return False


def _required_previous_part_nodes(
    nodes: list[dict[str, Any]], *, task_texts: list[str],
) -> list[dict[str, Any]]:
    """Keep explicit prior references without promoting adjacent context.

    previous_parts remains the source contract's data-flow declaration when
    the task does not enumerate a prior part.  When the task does name one or
    more entries, that explicit subset is authoritative.
    """
    referenced = [
        node
        for node in nodes
        if any(_mentions_previous_part(text, node) for text in task_texts)
    ]
    return referenced or nodes


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
    semantic_requirements = raw.get("semantic_requirements")
    if semantic_requirements is not None:
        if not isinstance(semantic_requirements, list) or not semantic_requirements or any(
            not isinstance(item, str) or not item.strip() for item in semantic_requirements
        ):
            raise SemanticDagError(f"requested_outputs[{index}].semantic_requirements is invalid")
        output["semantic_requirements"] = list(semantic_requirements)
        derive["semantic_requirements"] = list(semantic_requirements)
    return derive, output


def build_semantic_dag(
    *, record_id: str, problem_evidence: Mapping[str, Any],
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
    previous_nodes: list[dict[str, Any]] = []
    for index, raw in enumerate(previous):
        node = _previous_part_node(raw, index)
        if node["source_id"] in previous_source_ids:
            raise SemanticDagError("previous_parts contains duplicate source_id")
        previous_source_ids.add(node["source_id"])
        previous_nodes.append(node)

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
    task_texts = [str(problem_evidence["current_question"])] + [
        str(derive["source_requirement"]) for derive in derivations
    ]
    required_previous = _required_previous_part_nodes(
        previous_nodes, task_texts=task_texts,
    )
    nodes.extend(required_previous)
    input_ids.extend(node["id"] for node in required_previous)
    nodes.extend(derivations)
    nodes.extend(outputs)

    edges: list[dict[str, str]] = []
    for derive in derivations:
        for source_id in input_ids:
            edges.append({
                "from": source_id,
                "to": derive["id"],
                "kind": "source_support",
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
    """Return the compact controller-owned summary bound by Review."""
    if not isinstance(dag, Mapping):
        raise SemanticDagError("semantic DAG must be an object")
    forbidden = _answer_bearing_paths(dag, path="semantic_dag")
    if forbidden:
        raise SemanticDagError(
            "semantic DAG contains answer-bearing field(s): "
            + ", ".join(forbidden)
        )
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
    kinds: dict[str, int] = {}
    output_ids: list[str] = []
    previous_source_ids: list[str] = []
    for node in nodes:
        if not isinstance(node, Mapping):
            raise SemanticDagError("semantic DAG node is not an object")
        kind = _nonempty_string(node.get("kind"), label="semantic DAG node kind")
        kinds[kind] = kinds.get(kind, 0) + 1
        if kind == "requested_output":
            output_ids.append(
                _nonempty_string(
                    node.get("output_id"), label="semantic DAG output_id"
                )
            )
        elif kind == "previous_part_prerequisite":
            previous_source_ids.append(
                _nonempty_string(
                    node.get("source_id"),
                    label="semantic DAG previous source_id",
                )
            )
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
        "unresolved are obligations, never source conclusions. For each "
        "requested_output whose immutable audit_requirements contains "
        "image_component_accounting, inspect the bound images before doing "
        "arithmetic: first trace a connected whole-product topology across "
        "every bound image, including repeated units, terminal fragments, "
        "caps/adducts, assembly edges, and every bracket/connector/cross-"
        "boundary bond. A printed formula can be a residue rather than the "
        "whole product. Only after all outgoing bonds and the preceding-page "
        "unit pattern are resolved may the component ledger, combined formula "
        "or quantity, and Lean carrier be recorded. "
        "This opt-in obligation is mandatory and cannot be marked "
        "not_applicable.\n"
    )
