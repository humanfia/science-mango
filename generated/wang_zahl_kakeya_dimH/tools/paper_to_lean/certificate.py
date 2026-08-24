#!/usr/bin/env python3
"""Produce a source-pinned, kernel-audited finite Lean certificate.

This is the resource-bounded production entry point for the finite-order fragment used
by the Family6 work.  The JSON model is still a human-authored formalization
of the pinned excerpt; no claim is made that prose-to-AST translation is
automatic.

The manifest and source excerpt are read once.  Z3 is used only to discover
whether ``constraints and not claim`` is satisfiable.  Lean then checks the
generated theorem (or concrete counterexample), and verification succeeds
only when the certificate is unchanged, warning-free, and depends on no
axioms outside the standard Mathlib three.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SMT_OPERATORS = {
    "lt": "<",
    "le": "<=",
    "gt": ">",
    "ge": ">=",
    "eq": "=",
    "ne": "distinct",
    "not": "not",
    "implies": "=>",
    "iff": "=",
    "xor": "xor",
    "and": "and",
    "or": "or",
    "distinct": "distinct",
}


def smt_term(term: Any) -> str:
    if isinstance(term, bool):
        return "true" if term else "false"
    if isinstance(term, int):
        return str(term) if term >= 0 else f"(- {-term})"
    if isinstance(term, str):
        return term
    op = term["op"]
    rendered = [smt_term(arg) for arg in term["args"]]
    if op == "and" and not rendered:
        return "true"
    if op == "or" and not rendered:
        return "false"
    return f"({SMT_OPERATORS[op]} {' '.join(rendered)})"


def lean_int(value: int) -> str:
    return f"({value} : Int)" if value >= 0 else f"(-{-value} : Int)"


def lean_term(term: Any, values: dict[str, int] | None = None) -> str:
    if isinstance(term, bool):
        return "True" if term else "False"
    if isinstance(term, int):
        return lean_int(term)
    if isinstance(term, str):
        return lean_int(values[term]) if values is not None else term
    op = term["op"]
    rendered = [lean_term(arg, values) for arg in term["args"]]
    binary = {
        "lt": "<",
        "le": "≤",
        "gt": ">",
        "ge": "≥",
        "eq": "=",
        "ne": "≠",
        "implies": "→",
        "iff": "↔",
    }
    if op in binary:
        return f"({rendered[0]} {binary[op]} {rendered[1]})"
    if op == "not":
        return f"(¬ {rendered[0]})"
    if op == "and":
        return "True" if not rendered else "(" + " ∧ ".join(rendered) + ")"
    if op == "or":
        return "False" if not rendered else "(" + " ∨ ".join(rendered) + ")"
    if op == "xor":
        left, right = rendered
        return f"(¬ ({left} ↔ {right}))"
    if op == "distinct":
        pairs = [
            f"({rendered[i]} ≠ {rendered[j]})"
            for i in range(len(rendered))
            for j in range(i + 1, len(rendered))
        ]
        return "(" + " ∧ ".join(pairs) + ")"
    raise AssertionError(f"validated operator not rendered: {op}")


def parse_int_value(node: Any) -> int:
    if isinstance(node, str) and re.fullmatch(r"[0-9]+", node):
        return strict_int(int(node), "Z3 integer")
    if (
        isinstance(node, list)
        and len(node) == 2
        and node[0] == "-"
        and isinstance(node[1], str)
        and node[1].isdigit()
    ):
        return strict_int(-int(node[1]), "Z3 integer")
    raise SecureManifestError(f"unsupported Z3 integer value: {node!r}")


def parse_sexpressions(text: str) -> list[Any]:
    tokens = re.findall(r"\(|\)|[^\s()]+", text)
    index = 0

    def parse_one() -> Any:
        nonlocal index
        if index >= len(tokens):
            raise SecureManifestError("unexpected end of Z3 output")
        token = tokens[index]
        index += 1
        if token != "(":
            if token == ")":
                raise SecureManifestError("unexpected ')' in Z3 output")
            return token
        result: list[Any] = []
        while index < len(tokens) and tokens[index] != ")":
            result.append(parse_one())
        if index >= len(tokens):
            raise SecureManifestError("unclosed '(' in Z3 output")
        index += 1
        return result

    result: list[Any] = []
    while index < len(tokens):
        result.append(parse_one())
    return result



ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")
IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
GENERATED_HYPOTHESIS_RE = re.compile(r"^_?h[0-9]+$")
MAX_MANIFEST_BYTES = 1_000_000
MAX_SOURCE_BYTES = 8_000_000
MAX_PATTERN_LENGTH = 512
MAX_VARIABLES = 256
MAX_CONSTRAINTS = 20_000
MAX_AST_NODES = 200_000
MAX_AST_DEPTH = 128
MAX_INTEGER_DIGITS = 256
MAX_TEXT_FIELD = 4096
MAX_DISTINCT_ARITY = 64
MAX_RENDER_ATOMS = 250_000
MAX_CERTIFICATE_BYTES = 8_000_000

ROOT_FIELDS = {"source", "model"}
SOURCE_FIELDS = {
    "path",
    "start_line",
    "end_line",
    "start_regex",
    "end_regex",
    "locator",
    "url",
    "expected_sha256",
}
MODEL_FIELDS = {"name", "namespace", "variables", "constraints", "claim"}

RESERVED = {
    # Lean commands/terms and SMT-LIB reserved words relevant to this fragment.
    "abbrev",
    "alias",
    "as",
    "attribute",
    "axiom",
    "builtin_initialize",
    "by",
    "class",
    "def",
    "decreasing_by",
    "deriving",
    "do",
    "elab",
    "elab_rules",
    "else",
    "end",
    "example",
    "exists",
    "export",
    "extends",
    "fix",
    "false",
    "False",
    "forall",
    "from",
    "fun",
    "if",
    "infix",
    "infixl",
    "infixr",
    "initialize",
    "import",
    "in",
    "include",
    "inductive",
    "instance",
    "let",
    "macro",
    "macro_rules",
    "match",
    "mutual",
    "namespace",
    "notation",
    "open",
    "opaque",
    "par",
    "partial",
    "postfix",
    "prefix",
    "private",
    "protected",
    "section",
    "set_option",
    "structure",
    "syntax",
    "syntax_cat",
    "termination_by",
    "theorem",
    "then",
    "true",
    "True",
    "universe",
    "variables",
    "variable",
    "where",
    "Int",
    "Bool",
    "and",
    "or",
    "not",
    "distinct",
    "assert",
    "check-sat",
    "declare-const",
}


class SecureManifestError(ValueError):
    """The request cannot safely produce a certificate."""


@dataclass(frozen=True)
class SourceSnapshot:
    excerpt: str
    metadata: dict[str, Any]


@dataclass(frozen=True)
class ValidModel:
    name: str
    namespace: str
    variables: list[str]
    constraints: list[Any]
    claim: Any


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def reject_unknown_fields(value: dict[str, Any], allowed: set[str], label: str) -> None:
    unknown = sorted(set(value) - allowed)
    if unknown:
        raise SecureManifestError(f"unknown {label} fields: {unknown}")


def reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise SecureManifestError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def read_bytes_bounded(path: Path, limit: int, label: str) -> bytes:
    try:
        size = path.stat().st_size
        if size > limit:
            raise SecureManifestError(f"{label} exceeds the {limit}-byte limit")
        with path.open("rb") as stream:
            data = stream.read(limit + 1)
    except OSError as exc:
        raise SecureManifestError(f"cannot read {label} {path}: {exc}") from exc
    if len(data) > limit:
        raise SecureManifestError(f"{label} exceeds the {limit}-byte limit")
    return data


def read_manifest_once(path: Path) -> tuple[dict[str, Any], str]:
    raw = read_bytes_bounded(path, MAX_MANIFEST_BYTES, "manifest")
    try:
        text = raw.decode("utf-8")
        parsed = json.loads(text, object_pairs_hook=reject_duplicate_pairs)
    except (UnicodeDecodeError, ValueError, RecursionError) as exc:
        raise SecureManifestError(f"invalid UTF-8 JSON manifest: {exc}") from exc
    if not isinstance(parsed, dict):
        raise SecureManifestError("manifest root must be an object")
    reject_unknown_fields(parsed, ROOT_FIELDS, "manifest")
    if set(parsed) != ROOT_FIELDS:
        raise SecureManifestError("manifest must contain exactly source and model")
    return parsed, sha256_bytes(raw)


def require_string(value: Any, label: str, *, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        raise SecureManifestError(f"{label} must be a string")
    if "\x00" in value:
        raise SecureManifestError(f"{label} contains a NUL character")
    if not allow_empty and not value:
        raise SecureManifestError(f"{label} must not be empty")
    if len(value) > MAX_TEXT_FIELD:
        raise SecureManifestError(f"{label} exceeds {MAX_TEXT_FIELD} characters")
    return value


def require_identifier(value: Any, label: str) -> str:
    name = require_string(value, label)
    if (
        IDENTIFIER_RE.fullmatch(name) is None
        or name == "_"
        or name in RESERVED
        or GENERATED_HYPOTHESIS_RE.fullmatch(name) is not None
    ):
        raise SecureManifestError(f"{label} is not a safe Lean/SMT identifier: {name!r}")
    return name


def strict_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise SecureManifestError(f"{label} must be an integer")
    if len(str(abs(value))) > MAX_INTEGER_DIGITS:
        raise SecureManifestError(
            f"{label} exceeds the {MAX_INTEGER_DIGITS}-digit limit"
        )
    return value


def exact_line_marker(pattern: Any, label: str) -> str:
    value = require_string(pattern, label)
    if len(value) > MAX_PATTERN_LENGTH:
        raise SecureManifestError(f"{label} exceeds {MAX_PATTERN_LENGTH} characters")
    if not (value.startswith("^") and value.endswith("$")):
        raise SecureManifestError(f"{label} must be an exact ^...$ line marker")
    body = value[1:-1]
    if not body or re.search(r"[\\.*+?()[\]{}|^$]", body):
        raise SecureManifestError(
            f"{label} may not contain regular-expression operators"
        )
    return body


def resolve_source_path(manifest_path: Path, source_root: Path, raw_path: Any) -> Path:
    value = require_string(raw_path, "source.path")
    relative = Path(value)
    if relative.is_absolute():
        raise SecureManifestError("source.path must be relative")
    try:
        resolved = (manifest_path.parent / relative).resolve(strict=True)
    except (OSError, ValueError) as exc:
        raise SecureManifestError(f"cannot resolve source.path: {exc}") from exc
    try:
        resolved.relative_to(source_root)
    except ValueError as exc:
        raise SecureManifestError(
            f"source.path escapes source root {source_root}"
        ) from exc
    if not resolved.is_file():
        raise SecureManifestError("source.path must resolve to a regular file")
    return resolved


def extract_source_snapshot(
    manifest_path: Path, source_root: Path, raw: Any
) -> SourceSnapshot:
    if not isinstance(raw, dict):
        raise SecureManifestError("source must be an object")
    reject_unknown_fields(raw, SOURCE_FIELDS, "source")
    required = {"path", "expected_sha256"}
    if not required.issubset(raw):
        raise SecureManifestError("source.path and source.expected_sha256 are required")

    expected = raw["expected_sha256"]
    if not isinstance(expected, str) or SHA256_RE.fullmatch(expected) is None:
        raise SecureManifestError(
            "source.expected_sha256 must be an explicit 64-digit SHA-256"
        )

    path = resolve_source_path(manifest_path, source_root, raw["path"])
    data = read_bytes_bounded(path, MAX_SOURCE_BYTES, "source")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise SecureManifestError("source must be UTF-8 text") from exc

    has_lines = "start_line" in raw or "end_line" in raw
    has_markers = "start_regex" in raw or "end_regex" in raw
    if has_lines == has_markers:
        raise SecureManifestError(
            "source needs exactly one selector: line range or exact line markers"
        )

    if has_lines:
        if "start_line" not in raw or "end_line" not in raw:
            raise SecureManifestError("both source.start_line and source.end_line are required")
        lines = text.splitlines(keepends=True)
        start = strict_int(raw["start_line"], "source.start_line")
        end = strict_int(raw["end_line"], "source.end_line")
        if start < 1 or end < start or end > len(lines):
            raise SecureManifestError(
                f"invalid source line range {start}..{end} for {len(lines)} lines"
            )
        excerpt = "".join(lines[start - 1 : end])
        default_locator = f"lines {start}-{end}"
    else:
        if "start_regex" not in raw or "end_regex" not in raw:
            raise SecureManifestError(
                "both source.start_regex and source.end_regex are required"
            )
        start_marker = exact_line_marker(raw["start_regex"], "source.start_regex")
        end_marker = exact_line_marker(raw["end_regex"], "source.end_regex")
        lines = text.splitlines(keepends=True)
        plain = [line.rstrip("\r\n") for line in lines]
        try:
            start_index = plain.index(start_marker)
        except ValueError as exc:
            raise SecureManifestError(
                f"source start marker did not match: {start_marker!r}"
            ) from exc
        try:
            end_index = plain.index(end_marker, start_index + 1)
        except ValueError as exc:
            raise SecureManifestError(
                f"source end marker did not match after the start: {end_marker!r}"
            ) from exc
        # Match the pinned regex extractor boundary: include the end marker,
        # but not the line terminator following that marker.
        excerpt = (
            "".join(lines[start_index:end_index])
            + lines[end_index].rstrip("\r\n")
        )
        default_locator = f"exact lines {start_marker!r} .. {end_marker!r}"

    actual = sha256_text(excerpt)
    if actual.lower() != expected.lower():
        raise SecureManifestError(
            "source excerpt SHA-256 mismatch: "
            f"expected {expected.lower()}, got {actual.lower()}"
        )

    locator = raw.get("locator", default_locator)
    locator = require_string(locator, "source.locator")
    url = raw.get("url")
    if url is not None:
        url = require_string(url, "source.url")
    return SourceSnapshot(
        excerpt=excerpt,
        metadata={
            "path": str(path),
            "locator": locator,
            "url": url,
            "sha256": actual,
            "expected_sha256": expected.lower(),
        },
    )


def infer_sort(
    term: Any,
    variables: set[str],
    budget: list[int],
    depth: int = 0,
) -> str:
    if depth > MAX_AST_DEPTH:
        raise SecureManifestError(f"AST depth exceeds {MAX_AST_DEPTH}")
    budget[0] += 1
    budget[1] += 1
    if budget[0] > MAX_AST_NODES:
        raise SecureManifestError(f"AST node count exceeds {MAX_AST_NODES}")
    if budget[1] > MAX_RENDER_ATOMS:
        raise SecureManifestError(
            f"Lean render budget exceeds {MAX_RENDER_ATOMS} atoms"
        )

    if isinstance(term, bool):
        return "Bool"
    if isinstance(term, int):
        strict_int(term, "AST integer")
        return "Int"
    if isinstance(term, str):
        if term not in variables:
            raise SecureManifestError(f"unknown variable {term!r}")
        return "Int"
    if not isinstance(term, dict) or set(term) != {"op", "args"}:
        raise SecureManifestError(f"expression must have exactly op/args: {term!r}")
    op = term["op"]
    args = term["args"]
    if not isinstance(op, str) or not isinstance(args, list):
        raise SecureManifestError(f"malformed expression: {term!r}")

    fixed_arity = {
        "lt": 2,
        "le": 2,
        "gt": 2,
        "ge": 2,
        "eq": 2,
        "ne": 2,
        "not": 1,
        "implies": 2,
        "iff": 2,
        "xor": 2,
    }
    if op in fixed_arity and len(args) != fixed_arity[op]:
        raise SecureManifestError(f"operator {op!r} has invalid arity {len(args)}")
    if op in {"and", "or"}:
        pass
    elif op == "distinct":
        if len(args) < 2:
            raise SecureManifestError("operator 'distinct' needs at least two arguments")
        if len(args) > MAX_DISTINCT_ARITY:
            raise SecureManifestError(
                f"operator 'distinct' exceeds arity {MAX_DISTINCT_ARITY}"
            )
        budget[1] += len(args) * (len(args) - 1) // 2
        if budget[1] > MAX_RENDER_ATOMS:
            raise SecureManifestError(
                f"Lean render budget exceeds {MAX_RENDER_ATOMS} atoms"
            )
    elif op not in fixed_arity:
        raise SecureManifestError(f"unsupported operator {op!r}")

    sorts = [infer_sort(arg, variables, budget, depth + 1) for arg in args]
    if op in {"lt", "le", "gt", "ge", "distinct"}:
        if any(sort != "Int" for sort in sorts):
            raise SecureManifestError(f"operator {op!r} requires Int arguments")
        return "Bool"
    if op in {"eq", "ne"}:
        if sorts[0] != sorts[1]:
            raise SecureManifestError(f"operator {op!r} requires equal argument sorts")
        return "Bool"
    if op in {"not", "and", "or", "implies", "iff", "xor"}:
        if any(sort != "Bool" for sort in sorts):
            raise SecureManifestError(f"operator {op!r} requires Bool arguments")
        return "Bool"
    raise AssertionError(f"unhandled validated operator: {op}")


def validate_model(raw: Any) -> ValidModel:
    if not isinstance(raw, dict):
        raise SecureManifestError("model must be an object")
    reject_unknown_fields(raw, MODEL_FIELDS, "model")
    if not {"name", "variables", "constraints", "claim"}.issubset(raw):
        raise SecureManifestError(
            "model.name, variables, constraints, and claim are required"
        )
    name = require_identifier(raw["name"], "model.name")
    namespace = require_identifier(
        raw.get("namespace", "PaperToLeanCertificate"), "model.namespace"
    )
    variables_raw = raw["variables"]
    if not isinstance(variables_raw, list) or not variables_raw:
        raise SecureManifestError("model.variables must be a nonempty list")
    if len(variables_raw) > MAX_VARIABLES:
        raise SecureManifestError(f"model.variables exceeds {MAX_VARIABLES}")
    variables = [require_identifier(item, "model variable") for item in variables_raw]
    if len(set(variables)) != len(variables):
        raise SecureManifestError("model.variables contains duplicates")
    constraints = raw["constraints"]
    if not isinstance(constraints, list):
        raise SecureManifestError("model.constraints must be a list")
    if len(constraints) > MAX_CONSTRAINTS:
        raise SecureManifestError(f"model.constraints exceeds {MAX_CONSTRAINTS}")

    variable_set = set(variables)
    budget = [0, 0]
    for index, item in enumerate(constraints):
        if infer_sort(item, variable_set, budget) != "Bool":
            raise SecureManifestError(f"constraint {index} must have sort Bool")
    claim = raw["claim"]
    if infer_sort(claim, variable_set, budget) != "Bool":
        raise SecureManifestError("model.claim must have sort Bool")
    return ValidModel(name, namespace, variables, constraints, claim)


def escape_comment_field(value: Any) -> str:
    text = str(value).replace("\r", "\\r").replace("\n", "\\n")
    return text.replace("/-", "/ -").replace("-/", "- /")


def provenance_comment(metadata: dict[str, Any]) -> str:
    lines = [
        "/- Generated from a source-pinned, human-authored finite model.",
        f"Source: {escape_comment_field(metadata['path'])}",
        f"Locator: {escape_comment_field(metadata['locator'])}",
        f"SHA256: {escape_comment_field(metadata['sha256'])}",
    ]
    if metadata.get("url"):
        lines.append(f"URL: {escape_comment_field(metadata['url'])}")
    lines.append("-/")
    return "\n".join(lines)


def z3_query(model: ValidModel) -> str:
    lines = ["(set-logic QF_LIA)"]
    lines.extend(f"(declare-const {name} Int)" for name in model.variables)
    lines.extend(f"(assert {smt_term(item)})" for item in model.constraints)
    lines.extend([f"(assert (not {smt_term(model.claim)}))", "(check-sat)"])
    return "\n".join(lines) + "\n"


def run_process(
    command: list[str],
    *,
    timeout: int,
    cwd: Path | None = None,
    input_text: str | None = None,
    label: str,
) -> subprocess.CompletedProcess[str]:
    process = subprocess.Popen(
        command,
        cwd=cwd,
        stdin=subprocess.PIPE if input_text is not None else subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(input=input_text, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        raise SecureManifestError(
            f"{label} exceeded the {timeout}-second timeout; "
            "its process group was killed"
        ) from exc
    return subprocess.CompletedProcess(
        command, process.returncode, stdout, stderr
    )


def parse_z3_values(stdout: str, variables: list[str]) -> dict[str, int]:
    parsed = parse_sexpressions(stdout)
    value_lists = [node for node in parsed if isinstance(node, list)]
    if not value_lists:
        raise SecureManifestError(f"Z3 returned no model values: {stdout!r}")
    assignments = value_lists[-1]
    result: dict[str, int] = {}
    for assignment in assignments:
        if not isinstance(assignment, list) or len(assignment) != 2:
            raise SecureManifestError(f"malformed Z3 assignment: {assignment!r}")
        name = assignment[0]
        if not isinstance(name, str) or name not in variables:
            raise SecureManifestError(f"unexpected Z3 variable: {name!r}")
        result[name] = parse_int_value(assignment[1])
    missing = set(variables) - set(result)
    if missing:
        raise SecureManifestError(f"Z3 omitted values for {sorted(missing)}")
    return result


def solve(
    z3: str, model: ValidModel, timeout: int
) -> tuple[str, dict[str, int], str]:
    query = z3_query(model)
    checked = run_process(
        [z3, "-in", "-smt2"],
        timeout=timeout,
        input_text=query,
        label="Z3",
    )
    if checked.returncode != 0:
        raise SecureManifestError(f"Z3 failed: {checked.stderr or checked.stdout}")
    lines = checked.stdout.strip().splitlines()
    if not lines or lines[0] not in {"sat", "unsat", "unknown"}:
        raise SecureManifestError(f"unexpected Z3 status: {checked.stdout!r}")
    status = lines[0]
    if status == "unknown":
        raise SecureManifestError("Z3 returned unknown; no certificate was generated")
    if status == "unsat":
        return status, {}, query

    value_query = query.rsplit("(check-sat)", 1)[0]
    value_query += "(check-sat)\n(get-value (" + " ".join(model.variables) + "))\n"
    valued = run_process(
        [z3, "-in", "-smt2"],
        timeout=timeout,
        input_text=value_query,
        label="Z3 model extraction",
    )
    if valued.returncode != 0:
        raise SecureManifestError(
            f"Z3 model extraction failed: {valued.stderr or valued.stdout}"
        )
    value_lines = valued.stdout.strip().splitlines()
    if not value_lines or value_lines[0] != "sat":
        raise SecureManifestError(f"unexpected Z3 model response: {valued.stdout!r}")
    return status, parse_z3_values(valued.stdout, model.variables), query


def generate_lean(
    model: ValidModel,
    status: str,
    values: dict[str, int],
    metadata: dict[str, Any],
) -> tuple[str, str]:
    header = [
        "import Mathlib.Tactic",
        "",
        "set_option autoImplicit false",
        "",
        provenance_comment(metadata),
        f"namespace {model.namespace}",
        "",
    ]
    if status == "unsat":
        binders = " ".join(f"({name} : Int)" for name in model.variables)
        hypotheses = [
            f"    (_h{index} : {lean_term(item)})"
            for index, item in enumerate(model.constraints)
        ]
        theorem_lines = [f"theorem {model.name} {binders}"]
        theorem_lines.extend(hypotheses)
        theorem_lines.extend([f"    : {lean_term(model.claim)} := by", "  omega"])
        checked_name = model.name
    elif status == "sat":
        conjunction = {
            "op": "and",
            "args": [
                {"op": "and", "args": model.constraints},
                {"op": "not", "args": [model.claim]},
            ],
        }
        checked_name = model.name + "_counterexample"
        theorem_lines = [
            f"theorem {checked_name} :",
            f"    {lean_term(conjunction, values)} := by",
            "  norm_num",
        ]
    else:
        raise AssertionError(f"unhandled solver status: {status}")
    footer = [
        "",
        f"#print axioms {checked_name}",
        "",
        f"end {model.namespace}",
        "",
    ]
    return "\n".join(header + theorem_lines + footer), checked_name


def audit_axioms(
    output: str, qualified_theorem: str
) -> tuple[bool, list[str], str | None]:
    depends = re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.DOTALL
    )
    independent = re.findall(
        r"'([^']+)' does not depend on any axioms", output
    )
    records: list[tuple[str, str]] = depends + [(name, "") for name in independent]
    if len(records) != 1 or records[0][0] != qualified_theorem:
        return (
            False,
            [],
            "expected exactly one #print axioms result for " + qualified_theorem,
        )
    names = {
        item.strip() for item in records[0][1].split(",") if item.strip()
    }
    unexpected = sorted(names - ALLOWED_AXIOMS)
    if unexpected:
        return False, sorted(names), f"unexpected axioms: {unexpected}"
    return True, sorted(names), None


def write_new(path: Path, text: str) -> None:
    try:
        with path.open("x", encoding="utf-8", newline="") as stream:
            stream.write(text)
    except OSError as exc:
        raise SecureManifestError(f"cannot create artifact {path}: {exc}") from exc


def resolve_executable(value: str, label: str) -> str:
    value = require_string(value, f"{label} executable")
    try:
        found = shutil.which(value)
    except (OSError, ValueError) as exc:
        raise SecureManifestError(
            f"cannot resolve {label} executable {value!r}: {exc}"
        ) from exc
    if found is None:
        raise SecureManifestError(f"cannot find {label} executable: {value!r}")
    return str(Path(found).resolve())


def require_timeout(value: int, label: str) -> int:
    if value < 1 or value > 3600:
        raise SecureManifestError(f"{label} must be between 1 and 3600 seconds")
    return value


def resolve_existing_path(value: Any, label: str) -> Path:
    raw = require_string(value, label)
    try:
        return Path(raw).resolve(strict=True)
    except (OSError, ValueError) as exc:
        raise SecureManifestError(f"cannot resolve {label}: {exc}") from exc


def run(args: argparse.Namespace) -> int:
    manifest_path = resolve_existing_path(args.manifest, "manifest path")
    manifest, manifest_sha256 = read_manifest_once(manifest_path)

    source_root = (
        manifest_path.parent
        if args.source_root is None
        else resolve_existing_path(args.source_root, "--source-root")
    )
    if not source_root.is_dir():
        raise SecureManifestError("source root must be a directory")
    source = extract_source_snapshot(manifest_path, source_root, manifest["source"])
    model = validate_model(manifest["model"])

    project = resolve_existing_path(args.project, "--project")
    if not project.is_dir() or not (
        (project / "lakefile.toml").is_file() or (project / "lakefile.lean").is_file()
    ):
        raise SecureManifestError("--project must be a Lake project directory")
    z3 = resolve_executable(args.z3, "Z3")
    lake = resolve_executable(args.lake, "Lake")
    z3_timeout = require_timeout(args.z3_timeout, "--z3-timeout")
    lean_timeout = require_timeout(args.lean_timeout, "--lean-timeout")

    output_value = require_string(args.output, "--output")
    try:
        output = Path(output_value).absolute()
    except (OSError, ValueError) as exc:
        raise SecureManifestError(f"cannot resolve --output: {exc}") from exc
    if os.path.lexists(output):
        raise SecureManifestError("--output must name a fresh, nonexistent path")
    try:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.mkdir()
    except OSError as exc:
        raise SecureManifestError(f"cannot create output directory {output}: {exc}") from exc

    status, values, query = solve(z3, model, z3_timeout)
    lean_source, checked_name = generate_lean(model, status, values, source.metadata)
    if len(lean_source.encode("utf-8")) > MAX_CERTIFICATE_BYTES:
        raise SecureManifestError(
            f"certificate exceeds the {MAX_CERTIFICATE_BYTES}-byte limit"
        )
    certificate = output / "Certificate.lean"
    excerpt_path = output / "source_excerpt.txt"
    model_path = output / "model.smt2"
    report_path = output / "report.json"
    write_new(excerpt_path, source.excerpt)
    write_new(model_path, query)
    write_new(certificate, lean_source)

    certificate_before = sha256_text(lean_source)
    checked = run_process(
        [lake, "env", "lean", "-E", "warning", str(certificate)],
        timeout=lean_timeout,
        cwd=project,
        label="Lean",
    )
    certificate_after = sha256_bytes(
        read_bytes_bounded(certificate, MAX_CERTIFICATE_BYTES, "certificate")
    )
    unchanged = certificate_before == certificate_after
    combined = checked.stdout + checked.stderr
    warning_free = "warning:" not in combined.lower()
    qualified_theorem = f"{model.namespace}.{checked_name}"
    axiom_ok, axioms, audit_error = audit_axioms(combined, qualified_theorem)
    verified = checked.returncode == 0 and unchanged and warning_free and axiom_ok
    if not unchanged:
        audit_error = "Certificate.lean changed while Lean was checking it"
    elif not warning_free:
        audit_error = "Lean emitted warnings"
    elif checked.returncode != 0:
        audit_error = f"Lean exited with status {checked.returncode}"

    report = {
        "format": "paper-to-lean-certificate-v5",
        "semantic_scope": (
            "human-authored finite model tied to a pinned source excerpt; "
            "not automatic prose-to-AST extraction"
        ),
        "manifest": str(manifest_path),
        "manifest_sha256": manifest_sha256,
        "source_root": str(source_root),
        "source": source.metadata,
        "source_excerpt_sha256": sha256_text(source.excerpt),
        "model_smt2_sha256": sha256_text(query),
        "solver_status_for_constraints_and_not_claim": status,
        "counterexample": values if status == "sat" else None,
        "certificate": str(certificate),
        "certificate_theorem": qualified_theorem,
        "certificate_sha256": certificate_before,
        "certificate_unchanged_during_check": unchanged,
        "z3_executable": z3,
        "z3_timeout_seconds": z3_timeout,
        "lake_executable": lake,
        "lean_timeout_seconds": lean_timeout,
        "lean_returncode": checked.returncode,
        "lean_stdout": checked.stdout,
        "lean_stderr": checked.stderr,
        "lean_axioms": axioms,
        "lean_axiom_allowlist": sorted(ALLOWED_AXIOMS),
        "lean_axiom_audit_ok": axiom_ok,
        "lean_warning_free": warning_free,
        "lean_audit_error": audit_error,
        "lean_verified": verified,
    }
    write_new(report_path, json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if verified else 2


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description="Generate a source-pinned, Lean-kernel-audited finite certificate."
    )
    result.add_argument("manifest", help="strict JSON manifest")
    result.add_argument("--output", required=True, help="fresh artifact directory")
    result.add_argument("--project", default=".", help="Lake project used for Lean")
    result.add_argument(
        "--source-root",
        help="trusted source root (defaults to the manifest directory)",
    )
    result.add_argument("--z3", default="z3", help="Z3 executable")
    result.add_argument("--lake", default="lake", help="Lake executable")
    result.add_argument("--z3-timeout", type=int, default=60)
    result.add_argument("--lean-timeout", type=int, default=300)
    return result


def main() -> int:
    try:
        return run(parser().parse_args())
    except (SecureManifestError, OSError, ValueError) as exc:
        print(f"certificate: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
