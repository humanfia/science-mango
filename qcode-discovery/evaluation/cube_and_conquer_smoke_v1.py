"""Small proof-carrying Cube-and-Conquer demonstration.

This module is deliberately ``TEST_ONLY``.  It proves the mechanics needed by
the paper400 campaign without making a quantum-code claim:

* a full binary split tree is replayed as an exact, mutually-exclusive cover;
* every leaf is solved by a separate single-process CaDiCaL invocation;
* every UNSAT result carries both DRAT and converted LRAT evidence; and
* an aggregate is admitted only after fresh DRAT and LRAT replay for every
  leaf and exact hash binding of the cover, CNFs, tools, and proofs.

The outer worker pool may run leaves concurrently.  Solver instances never
share clauses, proof streams, or mutable state.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import os
import stat
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_VERSION = 1
COVER_KIND = "cube-and-conquer-smoke-cover-v1"
LEAF_KIND = "cube-and-conquer-smoke-leaf-proof-v1"
AGGREGATE_KIND = "cube-and-conquer-smoke-aggregate-v1"
VERIFICATION_KIND = "cube-and-conquer-smoke-verification-v1"
AUTHORITY = "TEST_ONLY"
CLASSIFICATION = "TEST_ONLY_PROOF_CARRYING_UNSAT"

EXPECTED_CADICAL_SHA256 = (
    "f8b70724eb0af0ea3b5c0c305fa6a959822ce680326f04ceee7b44ce970d1171"
)
EXPECTED_DRAT_TRIM_SHA256 = (
    "a48ebed7b4b6b373d3ddbeb3368dae7622a9e17bab7fe6eb751ab996757f9fbe"
)
EXPECTED_LRAT_CHECK_SHA256 = (
    "5b87b3ee157db3b1c6b0b70e23faa40ab123c8dd6db63d9518d64312da579517"
)
EXPECTED_CADICAL_VERSION = "1.9.5"

SOLVER_MARKER = b"s UNSATISFIABLE"
DRAT_MARKER = b"s VERIFIED"
LRAT_MARKER = b"c VERIFIED"
LOG_CAP_BYTES = 1 << 20
PROOF_CAP_BYTES = 64 << 20


class CubeAndConquerSmokeError(RuntimeError):
    """A cover, artifact, process, or proof invariant failed."""


@dataclass(frozen=True)
class CNF:
    num_variables: int
    clauses: tuple[tuple[int, ...], ...]


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


def _selfhash_valid(value: Any, field: str) -> bool:
    if type(value) is not dict:
        return False
    unsigned = dict(value)
    claimed = unsigned.pop(field, None)
    return type(claimed) is str and claimed == canonical_sha256(unsigned)


def _read_regular(path: Path, *, cap: int | None = None) -> bytes:
    target = Path(path)
    if target.is_symlink():
        raise CubeAndConquerSmokeError(f"symlink artifact rejected: {target}")
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(target, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise CubeAndConquerSmokeError(f"not a regular file: {target}")
        if cap is not None and before.st_size > cap:
            raise CubeAndConquerSmokeError(f"artifact exceeds cap: {target}")
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(1 << 20, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        payload = b"".join(chunks)
        after = os.fstat(descriptor)
        identity = lambda item: (
            item.st_dev,
            item.st_ino,
            item.st_mode,
            item.st_uid,
            item.st_size,
            item.st_mtime_ns,
            item.st_ctime_ns,
        )
        if identity(before) != identity(after) or len(payload) != before.st_size:
            raise CubeAndConquerSmokeError(f"artifact changed while read: {target}")
        return payload
    finally:
        os.close(descriptor)


def _write_new(path: Path, payload: bytes) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    try:
        with target.open("xb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    except FileExistsError as exc:
        raise CubeAndConquerSmokeError(f"refusing to overwrite: {target}") from exc


def _write_new_json(path: Path, value: Mapping[str, Any]) -> None:
    payload = json.dumps(
        value, sort_keys=True, indent=2, ensure_ascii=False, allow_nan=False
    ).encode("utf-8") + b"\n"
    _write_new(path, payload)


def _strict_json(path: Path) -> dict[str, Any]:
    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise CubeAndConquerSmokeError(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise CubeAndConquerSmokeError(f"non-finite JSON number: {value}")

    try:
        value = json.loads(
            _read_regular(path, cap=16 << 20).decode("utf-8"),
            object_pairs_hook=object_pairs,
            parse_constant=reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CubeAndConquerSmokeError(f"invalid JSON: {path}") from exc
    if type(value) is not dict:
        raise CubeAndConquerSmokeError(f"JSON root is not an object: {path}")
    return value


def parse_dimacs(payload: bytes) -> CNF:
    try:
        text = payload.decode("ascii")
    except UnicodeDecodeError as exc:
        raise CubeAndConquerSmokeError("DIMACS must be ASCII") from exc
    header: tuple[int, int] | None = None
    tokens: list[int] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("c"):
            continue
        fields = stripped.split()
        if fields[0] == "p":
            if header is not None or len(fields) != 4 or fields[1] != "cnf":
                raise CubeAndConquerSmokeError("invalid or duplicate DIMACS header")
            try:
                num_variables = int(fields[2])
                num_clauses = int(fields[3])
            except ValueError as exc:
                raise CubeAndConquerSmokeError("non-integer DIMACS header") from exc
            if num_variables < 0 or num_clauses < 0:
                raise CubeAndConquerSmokeError("negative DIMACS count")
            header = (num_variables, num_clauses)
            continue
        if header is None:
            raise CubeAndConquerSmokeError(
                f"clause before DIMACS header at line {line_number}"
            )
        try:
            tokens.extend(int(field) for field in fields)
        except ValueError as exc:
            raise CubeAndConquerSmokeError(
                f"non-integer DIMACS token at line {line_number}"
            ) from exc
    if header is None:
        raise CubeAndConquerSmokeError("missing DIMACS header")
    clauses: list[tuple[int, ...]] = []
    current: list[int] = []
    for literal in tokens:
        if literal == 0:
            clauses.append(tuple(current))
            current = []
        else:
            if abs(literal) > header[0]:
                raise CubeAndConquerSmokeError("DIMACS literal outside variable range")
            current.append(literal)
    if current:
        raise CubeAndConquerSmokeError("unterminated DIMACS clause")
    if len(clauses) != header[1]:
        raise CubeAndConquerSmokeError("DIMACS clause count mismatch")
    return CNF(header[0], tuple(clauses))


def render_dimacs(cnf: CNF) -> bytes:
    chunks = [f"p cnf {cnf.num_variables} {len(cnf.clauses)}\n".encode("ascii")]
    for clause in cnf.clauses:
        body = " ".join(str(literal) for literal in clause)
        chunks.append(f"{body}{' ' if body else ''}0\n".encode("ascii"))
    return b"".join(chunks)


def append_units(cnf: CNF, assumptions: Sequence[int]) -> CNF:
    return CNF(
        cnf.num_variables,
        cnf.clauses + tuple((int(literal),) for literal in assumptions),
    )


def assumptions_sha256(assumptions: Sequence[int]) -> str:
    return canonical_sha256({"assumptions": [int(item) for item in assumptions]})


def build_split_tree(split_variables: Sequence[int]) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    variables = tuple(int(variable) for variable in split_variables)
    nodes: list[dict[str, Any]] = []
    leaves: list[dict[str, Any]] = []

    def visit(depth: int, path: str, assumptions: tuple[int, ...]) -> None:
        node_id = "root" if not path else f"node-{path}"
        if depth == len(variables):
            leaf_id = f"leaf-{len(leaves):04d}"
            node = {
                "node_id": node_id,
                "assumptions": list(assumptions),
                "leaf_id": leaf_id,
            }
            nodes.append(node)
            leaves.append({
                "leaf_id": leaf_id,
                "node_id": node_id,
                "assumptions": list(assumptions),
                "assumptions_sha256": assumptions_sha256(assumptions),
            })
            return
        variable = variables[depth]
        false_path = path + "0"
        true_path = path + "1"
        nodes.append({
            "node_id": node_id,
            "assumptions": list(assumptions),
            "split_variable": variable,
            "false_child": f"node-{false_path}",
            "true_child": f"node-{true_path}",
        })
        visit(depth + 1, false_path, assumptions + (-variable,))
        visit(depth + 1, true_path, assumptions + (variable,))

    visit(0, "", ())
    return {
        "root": "root",
        "split_variables": list(variables),
        "nodes": nodes,
    }, leaves


def replay_split_tree(tree: Any, *, num_variables: int) -> dict[str, Any]:
    if type(tree) is not dict or set(tree) != {"root", "split_variables", "nodes"}:
        raise CubeAndConquerSmokeError("split tree field set mismatch")
    split_variables = tree["split_variables"]
    nodes = tree["nodes"]
    if type(split_variables) is not list or not split_variables:
        raise CubeAndConquerSmokeError("split variable list must be non-empty")
    if len(split_variables) > 12:
        raise CubeAndConquerSmokeError("smoke split depth exceeds 12")
    if any(type(variable) is not int for variable in split_variables):
        raise CubeAndConquerSmokeError("split variable type mismatch")
    if len(set(split_variables)) != len(split_variables):
        raise CubeAndConquerSmokeError("split variables are not unique")
    if any(variable <= 0 or variable > num_variables for variable in split_variables):
        raise CubeAndConquerSmokeError("split variable outside CNF range")
    if type(nodes) is not list or not nodes:
        raise CubeAndConquerSmokeError("split tree has no nodes")
    index: dict[str, dict[str, Any]] = {}
    for raw in nodes:
        if type(raw) is not dict or type(raw.get("node_id")) is not str:
            raise CubeAndConquerSmokeError("malformed split-tree node")
        node_id = raw["node_id"]
        if not node_id or node_id in index:
            raise CubeAndConquerSmokeError("duplicate or empty split-tree node id")
        index[node_id] = raw
    if tree["root"] != "root" or "root" not in index:
        raise CubeAndConquerSmokeError("split-tree root mismatch")

    visited: set[str] = set()
    leaves: list[dict[str, Any]] = []

    def visit(node_id: str, depth: int, expected: tuple[int, ...]) -> None:
        if node_id in visited:
            raise CubeAndConquerSmokeError("split tree is cyclic or has shared children")
        node = index.get(node_id)
        if node is None:
            raise CubeAndConquerSmokeError("split tree references a missing child")
        visited.add(node_id)
        if node.get("assumptions") != list(expected):
            raise CubeAndConquerSmokeError("node assumptions do not replay from tree")
        if depth == len(split_variables):
            if set(node) != {"node_id", "assumptions", "leaf_id"}:
                raise CubeAndConquerSmokeError("leaf node field set mismatch")
            leaf_id = node["leaf_id"]
            if type(leaf_id) is not str or not leaf_id:
                raise CubeAndConquerSmokeError("invalid leaf id")
            leaves.append({
                "leaf_id": leaf_id,
                "node_id": node_id,
                "assumptions": list(expected),
                "assumptions_sha256": assumptions_sha256(expected),
            })
            return
        if set(node) != {
            "node_id", "assumptions", "split_variable", "false_child", "true_child"
        }:
            raise CubeAndConquerSmokeError("internal node field set mismatch")
        variable = split_variables[depth]
        if node["split_variable"] != variable:
            raise CubeAndConquerSmokeError("split variable does not replay by depth")
        false_child = node["false_child"]
        true_child = node["true_child"]
        if type(false_child) is not str or type(true_child) is not str:
            raise CubeAndConquerSmokeError("child id type mismatch")
        if false_child == true_child:
            raise CubeAndConquerSmokeError("false and true edges share a child")
        visit(false_child, depth + 1, expected + (-variable,))
        visit(true_child, depth + 1, expected + (variable,))

    visit("root", 0, ())
    if visited != set(index):
        raise CubeAndConquerSmokeError("split tree contains unreachable nodes")
    leaf_ids = [leaf["leaf_id"] for leaf in leaves]
    if len(set(leaf_ids)) != len(leaf_ids):
        raise CubeAndConquerSmokeError("duplicate leaf id")
    if len(leaves) != 1 << len(split_variables):
        raise CubeAndConquerSmokeError("split tree is not exhaustive")

    pair_count = 0
    for left, right in itertools.combinations(leaves, 2):
        pair_count += 1
        right_literals = set(right["assumptions"])
        if not any(-literal in right_literals for literal in left["assumptions"]):
            raise CubeAndConquerSmokeError("two leaves are not mutually exclusive")
    return {
        "valid": True,
        "coverage_method": "full-binary-split-tree-induction-v1",
        "mutually_exclusive": True,
        "exhaustive": True,
        "leaf_count": len(leaves),
        "pair_count_checked": pair_count,
        "leaves": leaves,
    }


def _relative(root: Path, path: Path) -> str:
    try:
        relative = path.relative_to(root)
    except ValueError as exc:
        raise CubeAndConquerSmokeError("artifact escaped bundle root") from exc
    if not relative.parts or ".." in relative.parts:
        raise CubeAndConquerSmokeError("unsafe artifact path")
    return relative.as_posix()


def _artifact(root: Path, path: Path, *, cap: int | None = None) -> dict[str, Any]:
    payload = _read_regular(path, cap=cap)
    return {
        "relative_path": _relative(root, path),
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }


def _artifact_path(root: Path, record: Any) -> Path:
    if type(record) is not dict or set(record) != {"relative_path", "sha256", "bytes"}:
        raise CubeAndConquerSmokeError("artifact record field set mismatch")
    relative = record["relative_path"]
    if type(relative) is not str:
        raise CubeAndConquerSmokeError("artifact path type mismatch")
    candidate = Path(relative)
    if candidate.is_absolute() or not candidate.parts or ".." in candidate.parts:
        raise CubeAndConquerSmokeError("unsafe artifact path")
    path = root.joinpath(*candidate.parts)
    payload = _read_regular(path)
    if type(record["bytes"]) is not int or record["bytes"] != len(payload):
        raise CubeAndConquerSmokeError("artifact byte count mismatch")
    if type(record["sha256"]) is not str or record["sha256"] != hashlib.sha256(payload).hexdigest():
        raise CubeAndConquerSmokeError("artifact SHA-256 mismatch")
    return path


def _tool_record(path: Path, *, role: str, expected_sha256: str) -> dict[str, Any]:
    physical = Path(path).resolve(strict=True)
    payload = _read_regular(physical, cap=16 << 20)
    digest = hashlib.sha256(payload).hexdigest()
    if digest != expected_sha256:
        raise CubeAndConquerSmokeError(f"{role} executable hash mismatch")
    record: dict[str, Any] = {
        "role": role,
        "path": str(physical),
        "sha256": digest,
        "bytes": len(payload),
    }
    if role == "cadical":
        version = subprocess.run(
            [str(physical), "--version"],
            check=False,
            capture_output=True,
            timeout=10,
            env=_clean_environment(),
        )
        text = version.stdout.decode("ascii", errors="strict").strip()
        if version.returncode != 0 or version.stderr or text != EXPECTED_CADICAL_VERSION:
            raise CubeAndConquerSmokeError("CaDiCaL version probe mismatch")
        record["version"] = text
    return record


def build_toolchain(cadical: Path, drat_trim: Path, lrat_check: Path) -> dict[str, Any]:
    return seal({
        "cadical": _tool_record(
            cadical, role="cadical", expected_sha256=EXPECTED_CADICAL_SHA256
        ),
        "drat_trim": _tool_record(
            drat_trim, role="drat-trim", expected_sha256=EXPECTED_DRAT_TRIM_SHA256
        ),
        "lrat_check": _tool_record(
            lrat_check, role="lrat-check", expected_sha256=EXPECTED_LRAT_CHECK_SHA256
        ),
        "proof_format": "binary-drat+converted-ascii-lrat-v1",
    }, "toolchain_sha256")


def _clean_environment() -> dict[str, str]:
    return {
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
        "OMP_NUM_THREADS": "1",
        "OMP_THREAD_LIMIT": "1",
        "OPENBLAS_NUM_THREADS": "1",
        "MKL_NUM_THREADS": "1",
        "NUMEXPR_NUM_THREADS": "1",
    }


def _contains_line(payload: bytes, marker: bytes) -> bool:
    return marker in [line.strip() for line in payload.splitlines()]


def _run_command(argv: Sequence[str], *, cwd: Path, timeout_s: int) -> tuple[dict[str, Any], bytes, bytes]:
    command = [str(item) for item in argv]
    started = time.monotonic_ns()
    process = subprocess.Popen(
        command,
        cwd=cwd,
        env=_clean_environment(),
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout_s)
    except subprocess.TimeoutExpired:
        timed_out = True
        process.kill()
        stdout, stderr = process.communicate()
    ended = time.monotonic_ns()
    if len(stdout) > LOG_CAP_BYTES or len(stderr) > LOG_CAP_BYTES:
        raise CubeAndConquerSmokeError("process log exceeded smoke cap")
    return {
        "argv": command,
        "argv_sha256": canonical_sha256(command),
        "pid": process.pid,
        "started_monotonic_ns": started,
        "ended_monotonic_ns": ended,
        "exit_code": process.returncode,
        "timed_out": timed_out,
    }, stdout, stderr


def _run_logged(
    argv: Sequence[str], *, cwd: Path, timeout_s: int, stdout_path: Path, stderr_path: Path,
) -> tuple[dict[str, Any], bytes, bytes]:
    process, stdout, stderr = _run_command(argv, cwd=cwd, timeout_s=timeout_s)
    _write_new(stdout_path, stdout)
    _write_new(stderr_path, stderr)
    process["stdout"] = _artifact(cwd.parent.parent, stdout_path, cap=LOG_CAP_BYTES)
    process["stderr"] = _artifact(cwd.parent.parent, stderr_path, cap=LOG_CAP_BYTES)
    return process, stdout, stderr


def _require_process(
    process: Mapping[str, Any], stdout: bytes, stderr: bytes, *, exit_code: int, marker: bytes,
) -> None:
    if (
        process.get("timed_out") is not False
        or process.get("exit_code") != exit_code
        or stderr != b""
        or not _contains_line(stdout, marker)
    ):
        raise CubeAndConquerSmokeError(
            f"process did not reach required terminal {marker.decode('ascii')}"
        )


def _solve_leaf(
    *, root: Path, cover: Mapping[str, Any], leaf: Mapping[str, Any], toolchain: Mapping[str, Any], timeout_s: int,
) -> dict[str, Any]:
    leaf_id = leaf["leaf_id"]
    leaf_dir = root / "leaves" / leaf_id
    cnf_path = _artifact_path(root, leaf["derived_cnf"])
    drat_path = leaf_dir / "proof.drat"
    lrat_path = leaf_dir / "proof.lrat"

    solver_process, solver_stdout, solver_stderr = _run_logged(
        [toolchain["cadical"]["path"], "-q", str(cnf_path), str(drat_path)],
        cwd=leaf_dir,
        timeout_s=timeout_s,
        stdout_path=leaf_dir / "solver.stdout",
        stderr_path=leaf_dir / "solver.stderr",
    )
    _require_process(
        solver_process, solver_stdout, solver_stderr,
        exit_code=20, marker=SOLVER_MARKER,
    )
    drat = _artifact(root, drat_path, cap=PROOF_CAP_BYTES)
    if drat["bytes"] <= 0:
        raise CubeAndConquerSmokeError("CaDiCaL emitted an empty DRAT proof")

    conversion_process, conversion_stdout, conversion_stderr = _run_logged(
        [
            toolchain["drat_trim"]["path"], str(cnf_path), str(drat_path),
            "-L", str(lrat_path), "-t", str(timeout_s),
        ],
        cwd=leaf_dir,
        timeout_s=timeout_s,
        stdout_path=leaf_dir / "drat-to-lrat.stdout",
        stderr_path=leaf_dir / "drat-to-lrat.stderr",
    )
    _require_process(
        conversion_process, conversion_stdout, conversion_stderr,
        exit_code=0, marker=DRAT_MARKER,
    )
    lrat = _artifact(root, lrat_path, cap=PROOF_CAP_BYTES)
    if lrat["bytes"] <= 0:
        raise CubeAndConquerSmokeError("DRAT conversion emitted an empty LRAT proof")

    lrat_process, lrat_stdout, lrat_stderr = _run_logged(
        [toolchain["lrat_check"]["path"], str(cnf_path), str(lrat_path)],
        cwd=leaf_dir,
        timeout_s=timeout_s,
        stdout_path=leaf_dir / "lrat-check.stdout",
        stderr_path=leaf_dir / "lrat-check.stderr",
    )
    _require_process(
        lrat_process, lrat_stdout, lrat_stderr,
        exit_code=0, marker=LRAT_MARKER,
    )

    commit = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": LEAF_KIND,
        "state": "PROOF_CARRYING_UNSAT",
        "authority": AUTHORITY,
        "test_only": True,
        "publication_certificate": False,
        "cover_manifest_sha256": cover["manifest_sha256"],
        "base_dimacs_sha256": cover["base"]["canonical_dimacs"]["sha256"],
        "leaf_id": leaf_id,
        "assumptions": leaf["assumptions"],
        "assumptions_sha256": leaf["assumptions_sha256"],
        "derived_cnf": leaf["derived_cnf"],
        "toolchain_sha256": toolchain["toolchain_sha256"],
        "solver": solver_process,
        "drat": drat,
        "drat_to_lrat": conversion_process,
        "lrat": lrat,
        "lrat_check": lrat_process,
    }, "certificate_sha256")
    _write_new_json(leaf_dir / "COMMIT.json", commit)
    return commit


def _check_logged_process(
    root: Path, process: Any, *, exit_code: int, marker: bytes,
) -> None:
    expected_fields = {
        "argv", "argv_sha256", "pid", "started_monotonic_ns",
        "ended_monotonic_ns", "exit_code", "timed_out", "stdout", "stderr",
    }
    if type(process) is not dict or set(process) != expected_fields:
        raise CubeAndConquerSmokeError("stored process field set mismatch")
    if type(process["argv"]) is not list or process["argv_sha256"] != canonical_sha256(process["argv"]):
        raise CubeAndConquerSmokeError("stored process argv hash mismatch")
    if type(process["pid"]) is not int or process["pid"] <= 0:
        raise CubeAndConquerSmokeError("stored process PID invalid")
    if (
        type(process["started_monotonic_ns"]) is not int
        or type(process["ended_monotonic_ns"]) is not int
        or process["ended_monotonic_ns"] < process["started_monotonic_ns"]
    ):
        raise CubeAndConquerSmokeError("stored process timing invalid")
    stdout_path = _artifact_path(root, process["stdout"])
    stderr_path = _artifact_path(root, process["stderr"])
    _require_process(
        process,
        _read_regular(stdout_path, cap=LOG_CAP_BYTES),
        _read_regular(stderr_path, cap=LOG_CAP_BYTES),
        exit_code=exit_code,
        marker=marker,
    )


def _validate_leaf_commit(
    root: Path,
    commit: Any,
    *,
    cover: Mapping[str, Any],
    leaf: Mapping[str, Any],
    toolchain: Mapping[str, Any],
) -> tuple[Path, Path, Path]:
    expected_fields = {
        "schema_version", "kind", "state", "authority", "test_only",
        "publication_certificate", "cover_manifest_sha256",
        "base_dimacs_sha256", "leaf_id", "assumptions",
        "assumptions_sha256", "derived_cnf", "toolchain_sha256", "solver",
        "drat", "drat_to_lrat", "lrat", "lrat_check", "certificate_sha256",
    }
    if type(commit) is not dict or set(commit) != expected_fields:
        raise CubeAndConquerSmokeError("leaf certificate field set mismatch")
    if not _selfhash_valid(commit, "certificate_sha256"):
        raise CubeAndConquerSmokeError("leaf certificate self-hash mismatch")
    fixed = {
        "schema_version": SCHEMA_VERSION,
        "kind": LEAF_KIND,
        "state": "PROOF_CARRYING_UNSAT",
        "authority": AUTHORITY,
        "test_only": True,
        "publication_certificate": False,
        "cover_manifest_sha256": cover["manifest_sha256"],
        "base_dimacs_sha256": cover["base"]["canonical_dimacs"]["sha256"],
        "leaf_id": leaf["leaf_id"],
        "assumptions": leaf["assumptions"],
        "assumptions_sha256": leaf["assumptions_sha256"],
        "derived_cnf": leaf["derived_cnf"],
        "toolchain_sha256": toolchain["toolchain_sha256"],
    }
    for key, expected in fixed.items():
        if commit.get(key) != expected:
            raise CubeAndConquerSmokeError(f"leaf certificate {key} mismatch")
    cnf_path = _artifact_path(root, commit["derived_cnf"])
    drat_path = _artifact_path(root, commit["drat"])
    lrat_path = _artifact_path(root, commit["lrat"])
    if commit["drat"]["bytes"] <= 0 or commit["lrat"]["bytes"] <= 0:
        raise CubeAndConquerSmokeError("empty proof artifact")
    _check_logged_process(root, commit["solver"], exit_code=20, marker=SOLVER_MARKER)
    _check_logged_process(root, commit["drat_to_lrat"], exit_code=0, marker=DRAT_MARKER)
    _check_logged_process(root, commit["lrat_check"], exit_code=0, marker=LRAT_MARKER)
    return cnf_path, drat_path, lrat_path


def _fresh_replay(
    *, leaf_id: str, cnf_path: Path, drat_path: Path, lrat_path: Path,
    toolchain: Mapping[str, Any], timeout_s: int,
) -> dict[str, Any]:
    drat_process, drat_stdout, drat_stderr = _run_command(
        [
            toolchain["drat_trim"]["path"], str(cnf_path), str(drat_path),
            "-t", str(timeout_s),
        ],
        cwd=cnf_path.parent,
        timeout_s=timeout_s,
    )
    _require_process(
        drat_process, drat_stdout, drat_stderr,
        exit_code=0, marker=DRAT_MARKER,
    )
    lrat_process, lrat_stdout, lrat_stderr = _run_command(
        [toolchain["lrat_check"]["path"], str(cnf_path), str(lrat_path)],
        cwd=cnf_path.parent,
        timeout_s=timeout_s,
    )
    _require_process(
        lrat_process, lrat_stdout, lrat_stderr,
        exit_code=0, marker=LRAT_MARKER,
    )
    return {
        "leaf_id": leaf_id,
        "fresh_drat_verified": True,
        "fresh_lrat_verified": True,
        "drat_terminal": DRAT_MARKER.decode("ascii"),
        "lrat_terminal": LRAT_MARKER.decode("ascii"),
    }


def _validate_cover(
    root: Path, cover: Any, *, expected_toolchain: Mapping[str, Any],
) -> tuple[CNF, list[dict[str, Any]], dict[str, Any]]:
    expected_fields = {
        "schema_version", "kind", "authority", "test_only",
        "publication_certificate", "coverage_method", "base", "tree",
        "leaves", "execution", "toolchain", "manifest_sha256",
    }
    if type(cover) is not dict or set(cover) != expected_fields:
        raise CubeAndConquerSmokeError("cover manifest field set mismatch")
    if not _selfhash_valid(cover, "manifest_sha256"):
        raise CubeAndConquerSmokeError("cover manifest self-hash mismatch")
    fixed = {
        "schema_version": SCHEMA_VERSION,
        "kind": COVER_KIND,
        "authority": AUTHORITY,
        "test_only": True,
        "publication_certificate": False,
        "coverage_method": "full-binary-split-tree-induction-v1",
    }
    for key, expected in fixed.items():
        if cover.get(key) != expected:
            raise CubeAndConquerSmokeError(f"cover {key} mismatch")
    if cover["toolchain"] != expected_toolchain:
        raise CubeAndConquerSmokeError("cover toolchain binding mismatch")
    if type(cover["base"]) is not dict or set(cover["base"]) != {
        "source_sha256", "source_bytes", "canonical_dimacs",
        "num_variables", "num_clauses",
    }:
        raise CubeAndConquerSmokeError("base binding field set mismatch")
    base_path = _artifact_path(root, cover["base"]["canonical_dimacs"])
    base = parse_dimacs(_read_regular(base_path))
    if (
        cover["base"]["num_variables"] != base.num_variables
        or cover["base"]["num_clauses"] != len(base.clauses)
        or render_dimacs(base) != _read_regular(base_path)
    ):
        raise CubeAndConquerSmokeError("base canonical DIMACS mismatch")
    replay = replay_split_tree(cover["tree"], num_variables=base.num_variables)
    if replay["coverage_method"] != cover["coverage_method"]:
        raise CubeAndConquerSmokeError("coverage method mismatch")
    if cover["leaves"] != replay["leaves"]:
        # The derived-CNF records are added below, so compare the proof-critical
        # tree fields separately.
        if type(cover["leaves"]) is not list or len(cover["leaves"]) != len(replay["leaves"]):
            raise CubeAndConquerSmokeError("cover leaf set mismatch")
        for stored, derived in zip(cover["leaves"], replay["leaves"], strict=True):
            if type(stored) is not dict or set(stored) != set(derived) | {"derived_cnf"}:
                raise CubeAndConquerSmokeError("cover leaf field set mismatch")
            for key, expected in derived.items():
                if stored.get(key) != expected:
                    raise CubeAndConquerSmokeError("cover leaf does not replay from tree")
    for leaf in cover["leaves"]:
        expected_cnf = render_dimacs(append_units(base, leaf["assumptions"]))
        cnf_path = _artifact_path(root, leaf["derived_cnf"])
        if _read_regular(cnf_path) != expected_cnf:
            raise CubeAndConquerSmokeError("derived leaf CNF is not base plus units")
    return base, list(cover["leaves"]), replay


def compute_aggregate(
    root: Path,
    *,
    cadical: Path,
    drat_trim: Path,
    lrat_check: Path,
    timeout_s: int = 30,
) -> dict[str, Any]:
    target = Path(root).resolve(strict=True)
    toolchain = build_toolchain(cadical, drat_trim, lrat_check)
    cover = _strict_json(target / "cover.json")
    _, leaves, coverage = _validate_cover(
        target, cover, expected_toolchain=toolchain
    )
    commit_paths = sorted((target / "leaves").glob("*/COMMIT.json"))
    expected_paths = sorted(
        target / "leaves" / leaf["leaf_id"] / "COMMIT.json" for leaf in leaves
    )
    if commit_paths != expected_paths:
        raise CubeAndConquerSmokeError("leaf certificate set is missing or extra")
    certificate_bindings: list[dict[str, Any]] = []
    fresh_replays: list[dict[str, Any]] = []
    for leaf, commit_path in zip(leaves, expected_paths, strict=True):
        commit = _strict_json(commit_path)
        cnf_path, drat_path, lrat_path = _validate_leaf_commit(
            target,
            commit,
            cover=cover,
            leaf=leaf,
            toolchain=toolchain,
        )
        certificate_bindings.append({
            "leaf_id": leaf["leaf_id"],
            "certificate_sha256": commit["certificate_sha256"],
            "drat_sha256": commit["drat"]["sha256"],
            "lrat_sha256": commit["lrat"]["sha256"],
        })
        fresh_replays.append(_fresh_replay(
            leaf_id=leaf["leaf_id"],
            cnf_path=cnf_path,
            drat_path=drat_path,
            lrat_path=lrat_path,
            toolchain=toolchain,
            timeout_s=timeout_s,
        ))
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": AGGREGATE_KIND,
        "authority": AUTHORITY,
        "test_only": True,
        "publication_certificate": False,
        "scientific_claim": None,
        "cover_manifest_sha256": cover["manifest_sha256"],
        "toolchain_sha256": toolchain["toolchain_sha256"],
        "coverage": {
            key: coverage[key]
            for key in (
                "valid", "coverage_method", "mutually_exclusive", "exhaustive",
                "leaf_count", "pair_count_checked",
            )
        },
        "leaf_certificates": certificate_bindings,
        "fresh_proof_replays": fresh_replays,
        "classification": CLASSIFICATION,
    }, "aggregate_sha256")


def run_bundle(
    *,
    input_cnf: Path,
    output_root: Path,
    split_variables: Sequence[int],
    workers: int,
    cadical: Path,
    drat_trim: Path,
    lrat_check: Path,
    timeout_s: int = 30,
) -> dict[str, Any]:
    if type(workers) is not int or workers < 1:
        raise CubeAndConquerSmokeError("workers must be a positive integer")
    source = _read_regular(Path(input_cnf), cap=16 << 20)
    base = parse_dimacs(source)
    split = tuple(int(variable) for variable in split_variables)
    tree, tree_leaves = build_split_tree(split)
    replay = replay_split_tree(tree, num_variables=base.num_variables)
    if tree_leaves != replay["leaves"]:
        raise CubeAndConquerSmokeError("generated tree failed immediate replay")
    toolchain = build_toolchain(cadical, drat_trim, lrat_check)

    root = Path(output_root).resolve()
    try:
        root.mkdir(mode=0o700, parents=False, exist_ok=False)
    except FileExistsError as exc:
        raise CubeAndConquerSmokeError(f"output root already exists: {root}") from exc
    base_path = root / "base.cnf"
    _write_new(base_path, render_dimacs(base))
    leaves: list[dict[str, Any]] = []
    for leaf in tree_leaves:
        leaf_dir = root / "leaves" / leaf["leaf_id"]
        leaf_dir.mkdir(parents=True, exist_ok=False)
        cnf_path = leaf_dir / "leaf.cnf"
        _write_new(cnf_path, render_dimacs(append_units(base, leaf["assumptions"])))
        leaves.append({**leaf, "derived_cnf": _artifact(root, cnf_path)})

    cover = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": COVER_KIND,
        "authority": AUTHORITY,
        "test_only": True,
        "publication_certificate": False,
        "coverage_method": "full-binary-split-tree-induction-v1",
        "base": {
            "source_sha256": hashlib.sha256(source).hexdigest(),
            "source_bytes": len(source),
            "canonical_dimacs": _artifact(root, base_path),
            "num_variables": base.num_variables,
            "num_clauses": len(base.clauses),
        },
        "tree": tree,
        "leaves": leaves,
        "execution": {
            "workers": min(workers, len(leaves)),
            "model": "independent-single-process-leaf-solvers-v1",
            "clause_sharing": False,
            "shared_proof_stream": False,
        },
        "toolchain": toolchain,
    }, "manifest_sha256")
    _write_new_json(root / "cover.json", cover)

    worker_count = min(workers, len(leaves))
    with ThreadPoolExecutor(max_workers=worker_count) as executor:
        futures = [
            executor.submit(
                _solve_leaf,
                root=root,
                cover=cover,
                leaf=leaf,
                toolchain=toolchain,
                timeout_s=timeout_s,
            )
            for leaf in leaves
        ]
        for future in futures:
            future.result()

    aggregate = compute_aggregate(
        root,
        cadical=cadical,
        drat_trim=drat_trim,
        lrat_check=lrat_check,
        timeout_s=timeout_s,
    )
    _write_new_json(root / "aggregate.json", aggregate)
    return aggregate


def verify_bundle(
    root: Path,
    *,
    cadical: Path,
    drat_trim: Path,
    lrat_check: Path,
    timeout_s: int = 30,
    report_path: Path | None = None,
) -> dict[str, Any]:
    target = Path(root).resolve(strict=True)
    stored = _strict_json(target / "aggregate.json")
    if not _selfhash_valid(stored, "aggregate_sha256"):
        raise CubeAndConquerSmokeError("aggregate self-hash mismatch")
    fresh = compute_aggregate(
        target,
        cadical=cadical,
        drat_trim=drat_trim,
        lrat_check=lrat_check,
        timeout_s=timeout_s,
    )
    if stored != fresh:
        raise CubeAndConquerSmokeError("fresh aggregate replay mismatch")
    verification = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": VERIFICATION_KIND,
        "authority": AUTHORITY,
        "test_only": True,
        "publication_certificate": False,
        "aggregate_sha256": stored["aggregate_sha256"],
        "fresh_aggregate_replay_equal": True,
        "classification": CLASSIFICATION,
    }, "verification_sha256")
    if report_path is not None:
        destination = Path(report_path)
        if not destination.is_absolute():
            destination = target / destination
        _write_new_json(destination, verification)
    return verification
