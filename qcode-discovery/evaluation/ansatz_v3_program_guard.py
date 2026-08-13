"""Static capability guard for the ansatz-v3 mutable proposal function.

The search representation promises that literature anchors are unavailable
until post-seal calibration.  A prompt instruction alone cannot enforce that
boundary, so the evaluator validates the mutable AST before importing it.
The generator may perform deterministic in-memory combinatorics; it may not
import modules, perform I/O, introspect Python internals, or add top-level
execution inside the evolve block.
"""

from __future__ import annotations

import ast
from pathlib import Path
from typing import Any


EVOLVE_START = "# EVOLVE-BLOCK-START"
EVOLVE_END = "# EVOLVE-BLOCK-END"
MUTABLE_FUNCTION = "_generate_support_proposals"
TRUSTED_SEED = (
    Path(__file__).resolve().parent.parent
    / "evolve/seed_solution_twisted_torus_ansatz_v3.py"
)
FORBIDDEN_NAMES = frozenset({
    "__builtins__",
    "__import__",
    "breakpoint",
    "compile",
    "copyright",
    "credits",
    "dir",
    "eval",
    "exec",
    "exit",
    "getattr",
    "globals",
    "help",
    "input",
    "license",
    "locals",
    "memoryview",
    "open",
    "print",
    "quit",
    "setattr",
    "type",
    "vars",
})
ALLOWED_DIRECT_CALLS = frozenset({
    "abs",
    "all",
    "any",
    "bool",
    "dict",
    "enumerate",
    "filter",
    "float",
    "frozenset",
    "gcd",
    "int",
    "iter",
    "lcm",
    "len",
    "list",
    "map",
    "max",
    "min",
    "next",
    "range",
    "reversed",
    "set",
    "sorted",
    "str",
    "sum",
    "tuple",
    "zip",
})
ALLOWED_METHOD_CALLS = frozenset({
    "add",
    "append",
    "clear",
    "copy",
    "count",
    "discard",
    "extend",
    "get",
    "index",
    "insert",
    "intersection",
    "items",
    "keys",
    "pop",
    "remove",
    "reverse",
    "setdefault",
    "sort",
    "symmetric_difference",
    "union",
    "update",
    "values",
})


class AnsatzV3ProgramGuardError(ValueError):
    """Mutable ansatz code exceeds its preregistered capabilities."""


def _marker_lines(source: str) -> tuple[int, int]:
    lines = source.splitlines()
    starts = [index + 1 for index, line in enumerate(lines) if line.strip() == EVOLVE_START]
    ends = [index + 1 for index, line in enumerate(lines) if line.strip() == EVOLVE_END]
    if len(starts) != 1 or len(ends) != 1 or starts[0] >= ends[0]:
        raise AnsatzV3ProgramGuardError("evolve block markers are invalid")
    return starts[0], ends[0]


def _immutable_envelope(source: str) -> tuple[str, str]:
    """Return bytes-equivalent text outside the single mutable block."""

    start, end = _marker_lines(source)
    lines = source.splitlines(keepends=True)
    return "".join(lines[:start]), "".join(lines[end - 1:])


def _trusted_immutable_envelope() -> tuple[str, str]:
    try:
        trusted_source = TRUSTED_SEED.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise AnsatzV3ProgramGuardError(
            f"cannot read trusted ansatz-v3 seed: {exc}"
        ) from exc
    return _immutable_envelope(trusted_source)


def validate_ansatz_v3_program_source(source: str) -> dict[str, Any]:
    if not isinstance(source, str) or not source:
        raise AnsatzV3ProgramGuardError("ansatz-v3 source is empty")
    start, end = _marker_lines(source)
    if _immutable_envelope(source) != _trusted_immutable_envelope():
        raise AnsatzV3ProgramGuardError(
            "ansatz-v3 immutable wrapper differs from the trusted seed"
        )
    try:
        tree = ast.parse(source)
    except SyntaxError as exc:
        raise AnsatzV3ProgramGuardError(f"ansatz-v3 source is invalid: {exc}") from exc
    block_nodes = [
        node
        for node in tree.body
        if start < getattr(node, "lineno", -1) < end
    ]
    if (
        len(block_nodes) != 1
        or not isinstance(block_nodes[0], ast.FunctionDef)
        or block_nodes[0].name != MUTABLE_FUNCTION
        or block_nodes[0].decorator_list
        or getattr(block_nodes[0], "end_lineno", end) >= end
    ):
        raise AnsatzV3ProgramGuardError(
            "evolve block must contain only the undecorated support proposal function"
        )
    function = block_nodes[0]
    forbidden_nodes = (
        ast.AsyncFunctionDef,
        ast.Await,
        ast.ClassDef,
        ast.Delete,
        ast.Global,
        ast.Import,
        ast.ImportFrom,
        ast.Nonlocal,
        ast.Raise,
        ast.Try,
        ast.With,
        ast.AsyncWith,
        ast.Yield,
        ast.YieldFrom,
    )
    for node in ast.walk(function):
        if node is not function and isinstance(node, ast.FunctionDef):
            raise AnsatzV3ProgramGuardError("nested functions are not allowed")
        if isinstance(node, forbidden_nodes):
            raise AnsatzV3ProgramGuardError(
                f"mutable ansatz uses forbidden syntax: {type(node).__name__}"
            )
        if isinstance(node, ast.Name) and (
            node.id in FORBIDDEN_NAMES or node.id.startswith("__")
        ):
            raise AnsatzV3ProgramGuardError(
                f"mutable ansatz uses forbidden name: {node.id}"
            )
        if isinstance(node, ast.Attribute):
            if node.attr.startswith("_") or node.attr not in ALLOWED_METHOD_CALLS:
                raise AnsatzV3ProgramGuardError(
                    f"mutable ansatz accesses forbidden attribute: {node.attr}"
                )
        if isinstance(node, ast.Call):
            target = node.func
            if isinstance(target, ast.Name):
                if target.id not in ALLOWED_DIRECT_CALLS:
                    raise AnsatzV3ProgramGuardError(
                        f"mutable ansatz calls forbidden function: {target.id}"
                    )
            elif isinstance(target, ast.Attribute):
                if target.attr not in ALLOWED_METHOD_CALLS:
                    raise AnsatzV3ProgramGuardError(
                        f"mutable ansatz calls forbidden method: {target.attr}"
                    )
            else:
                raise AnsatzV3ProgramGuardError(
                    "mutable ansatz uses an indirect callable"
                )
    return {
        "schema_version": 1,
        "kind": "qcode-ansatz-v3-program-capability-guard",
        "mutable_function": MUTABLE_FUNCTION,
        "evolve_block_lines": [start, end],
        "anchor_manifest_readable": False,
        "imports_allowed": False,
        "filesystem_io_allowed": False,
        "network_io_allowed": False,
        "immutable_wrapper_bound": True,
        "direct_call_policy": "deterministic-allowlist-v1",
    }


def validate_ansatz_v3_program(path: Path) -> dict[str, Any]:
    path = Path(path)
    if path.is_symlink() or not path.is_file():
        raise AnsatzV3ProgramGuardError(
            f"ansatz-v3 program must be a regular file: {path}"
        )
    try:
        source = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise AnsatzV3ProgramGuardError(f"cannot read ansatz-v3 program: {exc}") from exc
    return validate_ansatz_v3_program_source(source)


__all__ = [
    "AnsatzV3ProgramGuardError",
    "validate_ansatz_v3_program",
    "validate_ansatz_v3_program_source",
]
