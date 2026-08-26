#!/usr/bin/env python3
"""Strict validator for the archon-physics thermalization research DAG.

Run this with the campaign engine's pinned Python environment so that the
family-level goal is parsed by Archon's existing strict ``ChemistryGoalIR``
loader.  The script is deliberately read-only.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any, Mapping

from archon.commands.loop.chemistry_goal import load_chemistry_goal


ID_RE = re.compile(r"^[a-z][a-z0-9_]*(?:\.[a-z][a-z0-9_]*)*$", re.ASCII)
SHA_RE = re.compile(r"^[0-9a-f]{64}$", re.ASCII)
MODULE_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_]*(?:/[A-Za-z][A-Za-z0-9_]*)*\.lean$")
DECL_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*$")

TOP_KEYS = {
    "schema_version",
    "kind",
    "dag_id",
    "family_goal",
    "root",
    "family_roots",
    "auxiliary_roots",
    "nodes",
}
NODE_KEYS = {
    "node_id",
    "family_id",
    "node_kind",
    "title",
    "statement",
    "dependencies",
    "represents",
    "citations",
    "trust",
    "status",
    "blocker",
    "lean_target",
    "verification",
}
FAMILY_GOAL_KEYS = {"goal_id", "spec_hash"}
DEPENDENCY_KEYS = {"node_id", "mode"}
CITATION_KEYS = {"source_id", "locator", "role"}
TARGET_KEYS = {"module_path", "declaration", "kind", "role"}
VERIFICATION_KEYS = {
    "campaign_id",
    "plan_hash",
    "certificate_hash",
    "certificate_file_sha256",
    "symbol_dag_hash",
    "symbol_dag_file_sha256",
    "api_lock_file_sha256",
    "module_source_sha256",
}

NODE_KINDS = {
    "definition",
    "external_claim",
    "hypothesis_interface",
    "theorem",
    "synthetic_root",
}
EDGE_MODES = {"requires", "assumes"}
CITATION_ROLES = {
    "statement",
    "proof",
    "model",
    "empirical",
    "limitation",
    "counterexample",
}
TRUST_CLASSES = {"open", "empirical", "literature", "kernel_conditional", "kernel"}
STATUSES = {"planned", "active", "grounded", "verified", "blocked"}
TARGET_ROLES = {"definition", "hypothesis_interface", "claim"}
TARGET_KINDS = {"module", "def", "structure", "class", "inductive", "theorem"}


class DagError(ValueError):
    pass


def fail(context: str, message: str) -> None:
    raise DagError(f"{context}: {message}")


def strict_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            fail("JSON", f"duplicate object key {key!r}")
        result[key] = value
    return result


def reject_constant(value: str) -> None:
    fail("JSON", f"non-finite number {value!r} is forbidden")


def load_json(path: Path) -> Mapping[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=strict_pairs,
            parse_constant=reject_constant,
        )
    except json.JSONDecodeError as exc:
        fail(str(path), f"invalid JSON at line {exc.lineno}, column {exc.colno}")
    if not isinstance(value, Mapping):
        fail(str(path), "top level must be an object")
    return value


def exact_keys(value: Mapping[str, Any], expected: set[str], context: str) -> None:
    missing = sorted(expected - set(value))
    unknown = sorted(set(value) - expected)
    if missing:
        fail(context, "missing field(s): " + ", ".join(missing))
    if unknown:
        fail(context, "unknown field(s): " + ", ".join(unknown))


def text(value: Any, context: str, *, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or value != value.strip():
        fail(context, "expected a whitespace-trimmed string")
    if not allow_empty and not value:
        fail(context, "expected a non-empty string")
    return value


def identifier(value: Any, context: str) -> str:
    result = text(value, context)
    if ID_RE.fullmatch(result) is None:
        fail(context, "expected a lowercase dot-separated ASCII identifier")
    return result


def digest(value: Any, context: str) -> str:
    result = text(value, context)
    if SHA_RE.fullmatch(result) is None:
        fail(context, "expected a lowercase SHA-256 digest")
    return result


def sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def canonical_sha256(value: Any) -> str:
    payload = json.dumps(
        value,
        sort_keys=True,
        ensure_ascii=False,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def topo_order(edges: Mapping[str, set[str]], context: str) -> tuple[str, ...]:
    remaining = {node: set(deps) for node, deps in edges.items()}
    order: list[str] = []
    while remaining:
        ready = sorted(node for node, deps in remaining.items() if not deps)
        if not ready:
            fail(context, "cycle involving: " + ", ".join(sorted(remaining)))
        order.extend(ready)
        ready_set = set(ready)
        remaining = {
            node: deps - ready_set
            for node, deps in remaining.items()
            if node not in ready_set
        }
    return tuple(order)


def transitive_family_ancestors(goal: Any) -> dict[str, set[str]]:
    families = goal.family_index
    result: dict[str, set[str]] = {}
    for family_id in families:
        seen: set[str] = set()
        pending = list(families[family_id].depends_on)
        while pending:
            item = pending.pop()
            if item in seen:
                continue
            seen.add(item)
            pending.extend(families[item].depends_on)
        result[family_id] = seen
    return result


def validate_source_snapshots(goal: Any, project_root: Path) -> None:
    for source in goal.source_corpus:
        path = project_root / source.reference
        if not path.is_file():
            fail(f"source {source.source_id!r}", f"missing local snapshot {path}")
        actual = sha256_file(path)
        if actual != source.sha256:
            fail(
                f"source {source.source_id!r}",
                f"SHA mismatch: expected {source.sha256}, got {actual}",
            )


def validate_verified_base(node: Mapping[str, Any], project_root: Path) -> None:
    verification = node["verification"]
    assert isinstance(verification, Mapping)
    certificate_path = project_root / ".archon/physics-rebuild/release-certificate.json"
    symbol_path = project_root / ".archon/physics-rebuild/lean-symbol-dag.json"
    api_lock_path = project_root / ".archon/physics-rebuild/api-lock.json"
    module_path = project_root / node["lean_target"]["module_path"]
    certificate = load_json(certificate_path)

    checks = {
        "plan_hash": certificate.get("plan_hash"),
        "certificate_hash": certificate.get("certificate_hash"),
        "symbol_dag_hash": certificate.get("symbol_dag_hash"),
        "certificate_file_sha256": sha256_file(certificate_path),
        "symbol_dag_file_sha256": sha256_file(symbol_path),
        "api_lock_file_sha256": sha256_file(api_lock_path),
        "module_source_sha256": sha256_file(module_path),
    }
    for field, actual in checks.items():
        if verification[field] != actual:
            fail(
                f"node {node['node_id']!r}.verification.{field}",
                f"expected live release value {actual}, got {verification[field]}",
            )
    entrypoint_sha = certificate.get("entrypoint", {}).get("source_sha256")
    if entrypoint_sha != verification["module_source_sha256"]:
        fail(f"node {node['node_id']!r}", "entrypoint source hash is not certificate-bound")


def validate(project_root: Path, goal_path: Path, dag_path: Path) -> dict[str, Any]:
    goal = load_chemistry_goal(goal_path)
    raw = load_json(dag_path)
    exact_keys(raw, TOP_KEYS, "theorem DAG")
    if raw["schema_version"] != 1:
        fail("theorem DAG.schema_version", "expected 1")
    if raw["kind"] != "archonphysics.theorem-dag":
        fail("theorem DAG.kind", "expected 'archonphysics.theorem-dag'")
    identifier(raw["dag_id"], "theorem DAG.dag_id")

    family_goal = raw["family_goal"]
    if not isinstance(family_goal, Mapping):
        fail("theorem DAG.family_goal", "expected an object")
    exact_keys(family_goal, FAMILY_GOAL_KEYS, "theorem DAG.family_goal")
    if family_goal["goal_id"] != goal.goal_id:
        fail("theorem DAG.family_goal.goal_id", "does not match global goal")
    if family_goal["spec_hash"] != goal.spec_hash:
        fail("theorem DAG.family_goal.spec_hash", "does not match global goal")

    if not isinstance(raw["nodes"], list) or not raw["nodes"]:
        fail("theorem DAG.nodes", "expected a non-empty array")
    nodes: dict[str, Mapping[str, Any]] = {}
    edges: dict[str, set[str]] = {}
    edge_modes: dict[tuple[str, str], str] = {}
    family_ids = set(goal.family_index)
    source_ids = set(goal.source_index)

    for index, node in enumerate(raw["nodes"]):
        context = f"theorem DAG.nodes[{index}]"
        if not isinstance(node, Mapping):
            fail(context, "expected an object")
        exact_keys(node, NODE_KEYS, context)
        node_id = identifier(node["node_id"], f"{context}.node_id")
        family_id = identifier(node["family_id"], f"{context}.family_id")
        if node_id in nodes:
            fail("theorem DAG.nodes", f"duplicate node {node_id!r}")
        if family_id not in family_ids:
            fail(context, f"unknown family {family_id!r}")
        if node["node_kind"] not in NODE_KINDS:
            fail(context, f"unknown node_kind {node['node_kind']!r}")
        if node["trust"] not in TRUST_CLASSES:
            fail(context, f"unknown trust class {node['trust']!r}")
        if node["status"] not in STATUSES:
            fail(context, f"unknown status {node['status']!r}")
        text(node["title"], f"{context}.title")
        text(node["statement"], f"{context}.statement")

        blocker = node["blocker"]
        if node["status"] == "blocked":
            text(blocker, f"{context}.blocker")
        elif blocker is not None:
            fail(context, "blocker must be null unless status is blocked")

        dependencies = node["dependencies"]
        if not isinstance(dependencies, list):
            fail(f"{context}.dependencies", "expected an array")
        dependency_ids: set[str] = set()
        for dep_index, dependency in enumerate(dependencies):
            dep_context = f"{context}.dependencies[{dep_index}]"
            if not isinstance(dependency, Mapping):
                fail(dep_context, "expected an object")
            exact_keys(dependency, DEPENDENCY_KEYS, dep_context)
            dependency_id = identifier(dependency["node_id"], f"{dep_context}.node_id")
            if dependency_id == node_id:
                fail(dep_context, "self-dependency is forbidden")
            if dependency_id in dependency_ids:
                fail(dep_context, f"duplicate dependency {dependency_id!r}")
            if dependency["mode"] not in EDGE_MODES:
                fail(dep_context, f"unknown mode {dependency['mode']!r}")
            dependency_ids.add(dependency_id)
            edge_modes[(node_id, dependency_id)] = dependency["mode"]

        represents = node["represents"]
        if represents is not None:
            represents = identifier(represents, f"{context}.represents")
            if represents == node_id:
                fail(context, "a node cannot represent itself")
            dependency_ids.add(represents)

        citations = node["citations"]
        if not isinstance(citations, list):
            fail(f"{context}.citations", "expected an array")
        for citation_index, citation in enumerate(citations):
            cite_context = f"{context}.citations[{citation_index}]"
            if not isinstance(citation, Mapping):
                fail(cite_context, "expected an object")
            exact_keys(citation, CITATION_KEYS, cite_context)
            source_id = identifier(citation["source_id"], f"{cite_context}.source_id")
            if source_id not in source_ids:
                fail(cite_context, f"unknown source {source_id!r}")
            text(citation["locator"], f"{cite_context}.locator")
            if citation["role"] not in CITATION_ROLES:
                fail(cite_context, f"unknown role {citation['role']!r}")

        target = node["lean_target"]
        if target is not None:
            if not isinstance(target, Mapping):
                fail(f"{context}.lean_target", "expected an object or null")
            exact_keys(target, TARGET_KEYS, f"{context}.lean_target")
            module_path = text(target["module_path"], f"{context}.lean_target.module_path")
            declaration = text(target["declaration"], f"{context}.lean_target.declaration")
            if MODULE_RE.fullmatch(module_path) is None:
                fail(context, f"invalid Lean module path {module_path!r}")
            if DECL_RE.fullmatch(declaration) is None:
                fail(context, f"invalid Lean declaration {declaration!r}")
            if target["kind"] not in TARGET_KINDS or target["kind"] == "axiom":
                fail(context, f"forbidden or unknown Lean target kind {target['kind']!r}")
            if target["role"] not in TARGET_ROLES:
                fail(context, f"unknown Lean target role {target['role']!r}")

        verification = node["verification"]
        if verification is not None:
            if not isinstance(verification, Mapping):
                fail(f"{context}.verification", "expected an object or null")
            exact_keys(verification, VERIFICATION_KEYS, f"{context}.verification")
            identifier(verification["campaign_id"], f"{context}.verification.campaign_id")
            for field in VERIFICATION_KEYS - {"campaign_id"}:
                digest(verification[field], f"{context}.verification.{field}")

        if node["node_kind"] == "external_claim":
            if node["trust"] not in {"open", "empirical", "literature"}:
                fail(context, "external claims cannot have kernel trust")
            if node["status"] == "verified":
                fail(context, "external claims cannot be verified")
            if target is not None or verification is not None:
                fail(context, "external claims cannot carry Lean release evidence")
            if node["status"] == "grounded" and not citations:
                fail(context, "a grounded external claim needs citations")
        elif node["status"] == "grounded":
            fail(context, "only external claims may have grounded status")

        if node["node_kind"] == "hypothesis_interface":
            if target is None or target["role"] != "hypothesis_interface":
                fail(context, "hypothesis interfaces need a matching Lean target")
            if target["kind"] not in {"def", "structure", "class", "inductive"}:
                fail(context, "hypothesis interfaces cannot target a theorem or module")

        if node["status"] == "verified":
            if target is None or verification is None:
                fail(context, "verified nodes need Lean target and release evidence")
            if node["trust"] not in {"kernel", "kernel_conditional"}:
                fail(context, "verified nodes need kernel trust")
        elif verification is not None:
            fail(context, "only verified nodes may carry release evidence")

        nodes[node_id] = node
        edges[node_id] = dependency_ids

    for node_id, dependencies in edges.items():
        unknown = sorted(dependencies - set(nodes))
        if unknown:
            fail(f"node {node_id!r}", "unknown dependencies: " + ", ".join(unknown))
    order = topo_order(edges, "theorem DAG")

    ancestors = transitive_family_ancestors(goal)
    for node_id, dependencies in edges.items():
        family_id = nodes[node_id]["family_id"]
        allowed_families = {family_id} | ancestors[family_id]
        for dependency_id in dependencies:
            dependency_family = nodes[dependency_id]["family_id"]
            if dependency_family not in allowed_families:
                fail(
                    f"node {node_id!r}",
                    f"cross-family edge to {dependency_id!r} violates the global family DAG",
                )

    root = identifier(raw["root"], "theorem DAG.root")
    if root not in nodes:
        fail("theorem DAG.root", f"unknown node {root!r}")
    if nodes[root]["family_id"] != goal.root:
        fail("theorem DAG.root", "root node is not in the global root family")

    family_roots = raw["family_roots"]
    if not isinstance(family_roots, Mapping):
        fail("theorem DAG.family_roots", "expected an object")
    ordinary_families = family_ids - {goal.root}
    if set(family_roots) != ordinary_families:
        missing = sorted(ordinary_families - set(family_roots))
        unknown = sorted(set(family_roots) - ordinary_families)
        fail(
            "theorem DAG.family_roots",
            f"must map every ordinary family exactly once; missing={missing}, unknown={unknown}",
        )
    for family_id, node_id in family_roots.items():
        node_id = identifier(node_id, f"theorem DAG.family_roots.{family_id}")
        if node_id not in nodes or nodes[node_id]["family_id"] != family_id:
            fail("theorem DAG.family_roots", f"{family_id!r} has invalid root {node_id!r}")
        family = goal.family_index[family_id]
        if family.status == "verified":
            node = nodes[node_id]
            if node["status"] != "verified" or node["trust"] != "kernel":
                fail(
                    "theorem DAG.family_roots",
                    f"verified family {family_id!r} lacks a verified kernel root",
                )

    auxiliaries = raw["auxiliary_roots"]
    if not isinstance(auxiliaries, list):
        fail("theorem DAG.auxiliary_roots", "expected an array")
    auxiliary_ids: list[str] = []
    for index, item in enumerate(auxiliaries):
        item = identifier(item, f"theorem DAG.auxiliary_roots[{index}]")
        if item not in nodes:
            fail("theorem DAG.auxiliary_roots", f"unknown node {item!r}")
        if item in auxiliary_ids:
            fail("theorem DAG.auxiliary_roots", f"duplicate node {item!r}")
        auxiliary_ids.append(item)

    def reachable(starts: list[str]) -> set[str]:
        seen: set[str] = set()
        pending = list(starts)
        while pending:
            item = pending.pop()
            if item in seen:
                continue
            seen.add(item)
            pending.extend(edges[item])
        return seen

    main_reachable = reachable([root])
    internal_nodes = {
        node_id for node_id, node in nodes.items() if node["node_kind"] != "external_claim"
    }
    missing_internal = sorted(internal_nodes - main_reachable)
    if missing_internal:
        fail("theorem DAG", "internal nodes not reachable from root: " + ", ".join(missing_internal))
    all_reachable = reachable([root, *auxiliary_ids])
    disconnected = sorted(set(nodes) - all_reachable)
    if disconnected:
        fail("theorem DAG", "disconnected nodes: " + ", ".join(disconnected))

    for node_id, node in nodes.items():
        if node["node_kind"] == "hypothesis_interface" and node["represents"] is not None:
            represented = nodes[node["represents"]]
            if represented["node_kind"] != "external_claim":
                fail(f"node {node_id!r}", "represents must point to an external claim")
            if represented["family_id"] != node["family_id"]:
                fail(f"node {node_id!r}", "represented claim must be in the same family")
        if node["status"] == "verified" and node["trust"] == "kernel_conditional":
            if not any(
                edge_modes.get((node_id, dependency_id)) == "assumes"
                for dependency_id in edges[node_id]
            ):
                fail(f"node {node_id!r}", "kernel_conditional node has no assumes edge")
        if node["status"] == "verified" and node["trust"] == "kernel":
            if any(
                edge_modes.get((node_id, dependency_id)) == "assumes"
                for dependency_id in edges[node_id]
            ):
                fail(f"node {node_id!r}", "kernel node has an unresolved assumes edge")

    validate_source_snapshots(goal, project_root)
    for node in nodes.values():
        if node["status"] == "verified":
            validate_verified_base(node, project_root)

    spec_nodes = []
    for node in raw["nodes"]:
        spec_nodes.append({
            key: value
            for key, value in node.items()
            if key not in {"trust", "status", "blocker", "verification"}
        })
    spec_payload = {
        key: value
        for key, value in raw.items()
        if key != "nodes"
    }
    spec_payload["nodes"] = spec_nodes
    return {
        "valid": True,
        "goal_id": goal.goal_id,
        "goal_spec_hash": goal.spec_hash,
        "goal_state_hash": goal.state_hash,
        "dag_id": raw["dag_id"],
        "dag_spec_hash": canonical_sha256(spec_payload),
        "dag_state_hash": canonical_sha256(raw),
        "node_count": len(nodes),
        "main_reachable_count": len(main_reachable),
        "auxiliary_root_count": len(auxiliary_ids),
        "topological_order": list(order),
        "status_counts": dict(sorted(Counter(node["status"] for node in nodes.values()).items())),
        "trust_counts": dict(sorted(Counter(node["trust"] for node in nodes.values()).items())),
        "blocked_nodes": sorted(
            node_id for node_id, node in nodes.items() if node["status"] == "blocked"
        ),
        "family_frontier": list(goal.frontier()),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--goal", type=Path, default=Path("campaign/global-goal.json"))
    parser.add_argument("--dag", type=Path, default=Path("campaign/theorem-dag.json"))
    args = parser.parse_args()
    project_root = args.project.resolve()
    goal_path = args.goal if args.goal.is_absolute() else project_root / args.goal
    dag_path = args.dag if args.dag.is_absolute() else project_root / args.dag
    try:
        report = validate(project_root, goal_path, dag_path)
    except (DagError, OSError, ValueError) as exc:
        print(json.dumps({"valid": False, "error": str(exc)}, ensure_ascii=False, indent=2))
        return 1
    print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
