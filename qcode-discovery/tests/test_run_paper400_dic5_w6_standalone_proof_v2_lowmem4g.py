from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import signal
import subprocess
import time
import stat
import sys
from pathlib import Path
import pytest

SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "run_paper400_dic5_w6_standalone_proof_v2_lowmem4g.py"
)
SPEC = importlib.util.spec_from_file_location("n400_proof_runner_v2_lowmem4g", SOURCE)
assert SPEC is not None and SPEC.loader is not None
proof = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(proof)


def test_lowmem_policy_identity_is_explicit_and_original_is_preserved() -> None:
    original = SOURCE.with_name("run_paper400_dic5_w6_standalone_proof_v2.py")
    assert proof.RESOURCE_MIN_RAW_HEADROOM == 0
    assert proof.RESOURCE_MIN_EFFECTIVE_HEADROOM == 16 << 30
    assert proof.GATE.endswith("-v2-no-raw-admission")
    assert proof.RUNNER_RELATIVE_PATH.endswith("_v2_lowmem4g.py")
    assert hashlib.sha256(original.read_bytes()).hexdigest() == (
        "1034c232eae3bd131e988771673e2c4890c869658c8b380d9703a99d154c99cb"
    )


def test_import_is_stdlib_only_and_no_solver_or_science_import() -> None:
    source = SOURCE.read_text(encoding="utf-8")
    prefix = source.split("def _builder_helper", 1)[0]
    assert "import numpy" not in prefix
    assert "import pysat" not in prefix
    assert "solve_root(" not in source.split('if __name__ == "__main__":', 1)[1]
    assert "paper400_dic5_cube16" not in source


def test_canonical_json_is_type_strict_and_duplicate_safe() -> None:
    value = proof.seal({"value": 1, "flag": True})
    payload = proof.canonical_bytes(value) + b"\n"
    assert proof._decode_json(payload, canonical=True) == value
    assert proof.selfhash_valid(value)
    changed = dict(value)
    changed["value"] = True
    assert not proof.json_type_equal(changed, value)
    with pytest.raises(proof.ProofRunnerError):
        proof._decode_json(b'{"x":1,"x":1}\n', canonical=False)
    with pytest.raises(proof.ProofRunnerError):
        proof._decode_json(b'{"x":NaN}\n', canonical=False)
    with pytest.raises(proof.ProofRunnerError):
        proof._decode_json(b'{ "x":1}\n', canonical=True)


@pytest.mark.parametrize(
    ("payload", "expected"),
    [
        (b"s UNSATISFIABLE\n", [b"s UNSATISFIABLE"]),
        (b"c note\ns SATISFIABLE\nv 1 -2 0\n", [b"s SATISFIABLE"]),
        (b"s UNSATISFIABLE\ns SATISFIABLE\n", [b"s UNSATISFIABLE", b"s SATISFIABLE"]),
        (b"S UNSATISFIABLE\n", []),
        (b" s UNSATISFIABLE\n", []),
        (b"s UNSATISFIABLE\x00\n", [b"s UNSATISFIABLE\x00"]),
        (b"\xff\n", []),
    ],
)
def test_status_parser_is_raw_line_exact(payload: bytes, expected: list[bytes]) -> None:
    assert proof._status_lines(payload) == expected


def test_complete_model_parser_rejects_partial_duplicate_and_garbage() -> None:
    assert proof._parse_complete_model(
        b"s SATISFIABLE\nv 1 -2 3 0\n", num_variables=3,
    ) == [1, 0, 1]
    bad = [
        b"s SATISFIABLE\nv 1 -2 0\n",
        b"s SATISFIABLE\nv 1 -1 2 0\n",
        b"s SATISFIABLE\nv 1 2 4 0\n",
        b"s SATISFIABLE\nv 1 0 2 3\n",
        b"s SATISFIABLE\nv 1 2 3 0 junk\n",
        b"s SATISFIABLE\ns SATISFIABLE\nv 1 2 3 0\n",
        b"s SATISFIABLE\nx 1 2 3 0\n",
    ]
    for payload in bad:
        with pytest.raises(proof.ProofRunnerError):
            proof._parse_complete_model(payload, num_variables=3)


def test_atomic_publish_is_no_replace_and_rejects_symlink(tmp_path: Path) -> None:
    root = tmp_path / "root"
    root.mkdir(mode=0o700)
    target = proof._atomic_publish_bytes(root, "x", b"first")
    assert target.read_bytes() == b"first"
    assert stat.S_IMODE(target.stat().st_mode) == 0o600
    with pytest.raises(FileExistsError):
        proof._atomic_publish_bytes(root, "x", b"second")
    link = root / "link"
    link.symlink_to(target)
    with pytest.raises((OSError, proof.ProofRunnerError)):
        proof._safe_open_regular(link)


def test_memfd_is_sealed_and_byte_exact(tmp_path: Path) -> None:
    source = tmp_path / "payload"
    source.write_bytes(b"abc")
    fd, record = proof._seal_memfd_from_path(
        source,
        expected_sha256=hashlib.sha256(b"abc").hexdigest(),
        expected_bytes=3,
        executable=False,
    )
    try:
        assert os.read(fd, 3) == b"abc"
        assert record["sealed_memfd"] is True
        with pytest.raises(OSError):
            os.write(fd, b"x")
    finally:
        os.close(fd)


def test_bounded_process_accepts_exact_and_rejects_overflow(tmp_path: Path) -> None:
    clean, stdout, stderr = proof._run_capped_process(
        [sys.executable, "-I", "-B", "-c", "print('s UNSATISFIABLE')"],
        timeout_s=5,
        stdout_cap=1024,
        stderr_cap=1024,
        cwd=tmp_path,
        file_size_cap=1024,
    )
    assert proof._process_clean(clean, rc=0)
    assert stdout == b"s UNSATISFIABLE\n"
    assert stderr == b""
    overflow, captured, _ = proof._run_capped_process(
        [sys.executable, "-I", "-B", "-c", "print('x'*4096)"],
        timeout_s=5,
        stdout_cap=32,
        stderr_cap=32,
        cwd=tmp_path,
        file_size_cap=4096,
    )
    assert overflow["stdout_overflow"] is True
    assert len(captured) == 32
    assert not proof._process_clean(overflow, rc=0)


def test_bounded_process_timeout_is_unresolved(tmp_path: Path) -> None:
    result, _, _ = proof._run_capped_process(
        [sys.executable, "-I", "-B", "-c", "import time; time.sleep(30)"],
        timeout_s=1,
        stdout_cap=32,
        stderr_cap=32,
        cwd=tmp_path,
        file_size_cap=1024,
    )
    assert result["timed_out"] is True
    assert not proof._process_clean(result, rc=0)


def test_pinned_toolchain_policy_replays_without_n400() -> None:
    record = proof._toolchain_binding()
    assert record["solver"]["sha256"] == proof.EXPECTED_SOLVER_SHA256
    assert record["trusted_checker_policy_sha256"] == (
        proof.EXPECTED_POLICY_CANONICAL_SHA256
    )
    assert record["drat_trim"]["sha256"] == proof.EXPECTED_DRAT_TRIM_SHA256
    assert record["lrat_check"]["sha256"] == proof.EXPECTED_LRAT_CHECK_SHA256
    assert "static binary" not in record["authority_wording"]


def test_actual_toy_standalone_drat_lrat_chain(tmp_path: Path) -> None:
    # Complete contradictory 2-CNF; proof steps, not contradictory input units,
    # are required.  No n400 source or CNF is loaded in this test.
    cnf = tmp_path / "toy.cnf"
    cnf.write_bytes(b"p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
    cnf_sha = hashlib.sha256(cnf.read_bytes()).hexdigest()
    solver_fd, _ = proof._seal_memfd_from_path(
        proof.SOLVER_PATH,
        expected_sha256=proof.EXPECTED_SOLVER_SHA256,
        expected_bytes=proof.EXPECTED_SOLVER_BYTES,
        executable=True,
    )
    cnf_fd, _ = proof._seal_memfd_from_path(
        cnf, expected_sha256=cnf_sha,
        expected_bytes=cnf.stat().st_size,
        executable=False,
    )
    drat_fd, drat_private = proof._create_private_output(tmp_path, "toy.drat")
    try:
        process, stdout, stderr = proof._run_capped_process(
            [
                f"/proc/self/fd/{solver_fd}", "-q",
                f"/proc/self/fd/{cnf_fd}", f"/proc/self/fd/{drat_fd}",
            ],
            timeout_s=10,
            stdout_cap=4096,
            stderr_cap=4096,
            cwd=tmp_path,
            pass_fds=(solver_fd, cnf_fd, drat_fd),
            file_size_cap=1 << 20,
            watched_fds=((drat_fd, 1 << 20),),
        )
        assert proof._solver_semantics(
            process, stdout, stderr, expected="UNSATISFIABLE",
        )
        _assert_clean_supervised_record(process, rc=20)
        drat_sha, drat_bytes, _ = proof._hash_fd_stable(drat_fd, cap=1 << 20)
        assert drat_bytes > 0
        proof._publish_private_output(
            tmp_path, drat_private, drat_fd, "toy.drat",
            expected_sha256=drat_sha, expected_bytes=drat_bytes,
        )
        drat_fd = -1
    finally:
        os.close(solver_fd)
        os.close(cnf_fd)
        if drat_fd >= 0:
            proof._discard_private(tmp_path, drat_private, drat_fd)

    checker_fd, _ = proof._seal_memfd_from_path(
        proof.DRAT_TRIM_PATH,
        expected_sha256=proof.EXPECTED_DRAT_TRIM_SHA256,
        expected_bytes=None,
        executable=True,
    )
    cnf_fd, _ = proof._seal_memfd_from_path(
        cnf, expected_sha256=cnf_sha,
        expected_bytes=cnf.stat().st_size,
        executable=False,
    )
    raw_drat_fd = proof._safe_open_regular(tmp_path / "toy.drat")
    lrat_fd, lrat_private = proof._create_private_output(tmp_path, "toy.lrat")
    try:
        conversion, stdout, stderr = proof._run_capped_process(
            [
                f"/proc/self/fd/{checker_fd}", f"/proc/self/fd/{cnf_fd}",
                f"/proc/self/fd/{raw_drat_fd}", "-L",
                f"/proc/self/fd/{lrat_fd}", "-t", "10",
            ],
            timeout_s=10,
            stdout_cap=1 << 20,
            stderr_cap=1 << 20,
            cwd=tmp_path,
            pass_fds=(checker_fd, cnf_fd, raw_drat_fd, lrat_fd),
            file_size_cap=1 << 20,
            watched_fds=((lrat_fd, 1 << 20),),
        )
        assert proof._checker_success(
            conversion, stdout, stderr, marker=b"s VERIFIED",
        )
        _assert_clean_supervised_record(conversion, rc=0)
        lrat_sha, lrat_bytes, _ = proof._hash_fd_stable(lrat_fd, cap=1 << 20)
        assert lrat_bytes > 0
        proof._publish_private_output(
            tmp_path, lrat_private, lrat_fd, "toy.lrat",
            expected_sha256=lrat_sha, expected_bytes=lrat_bytes,
        )
        lrat_fd = -1
    finally:
        for descriptor in (checker_fd, cnf_fd, raw_drat_fd):
            os.close(descriptor)
        if lrat_fd >= 0:
            proof._discard_private(tmp_path, lrat_private, lrat_fd)

    lrat_checker_fd, _ = proof._seal_memfd_from_path(
        proof.LRAT_CHECK_PATH,
        expected_sha256=proof.EXPECTED_LRAT_CHECK_SHA256,
        expected_bytes=None,
        executable=True,
    )
    cnf_fd = proof._safe_open_regular(cnf)
    lrat_input_fd = proof._safe_open_regular(tmp_path / "toy.lrat")
    try:
        checked, stdout, stderr = proof._run_capped_process(
            [
                f"/proc/self/fd/{lrat_checker_fd}",
                f"/proc/self/fd/{cnf_fd}", f"/proc/self/fd/{lrat_input_fd}",
            ],
            timeout_s=10,
            stdout_cap=1 << 20,
            stderr_cap=1 << 20,
            cwd=tmp_path,
            pass_fds=(lrat_checker_fd, cnf_fd, lrat_input_fd),
            file_size_cap=1 << 20,
        )
        assert proof._checker_success(
            checked, stdout, stderr, marker=b"c VERIFIED",
        )
        _assert_clean_supervised_record(checked, rc=0)
    finally:
        for descriptor in (lrat_checker_fd, cnf_fd, lrat_input_fd):
            os.close(descriptor)


def test_tampered_toy_proof_fails_checker(tmp_path: Path) -> None:
    cnf = tmp_path / "toy.cnf"
    cnf.write_bytes(
        b"p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
    )
    bad = tmp_path / "bad.drat"
    bad.write_bytes(b"not-a-proof\n")
    process, stdout, stderr = proof._run_capped_process(
        [str(proof.DRAT_TRIM_PATH), str(cnf), str(bad), "-t", "5"],
        timeout_s=5,
        stdout_cap=1 << 20,
        stderr_cap=1 << 20,
        cwd=tmp_path,
        file_size_cap=1 << 20,
    )
    assert not proof._checker_success(
        process, stdout, stderr, marker=b"s VERIFIED",
    )


def test_checker_executes_through_private_sealed_runtime(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    (tmp_path / "static").mkdir()
    cnf = b"p cnf 1 2\n1 0\n-1 0\n"
    (tmp_path / proof.STATIC_DIMACS).write_bytes(cnf)
    drat = tmp_path / "toy.drat"
    drat.write_bytes(b"")
    monkeypatch.setattr(
        proof, "EXPECTED_BASE_DIMACS_SHA256", hashlib.sha256(cnf).hexdigest(),
    )
    monkeypatch.setattr(proof, "EXPECTED_BASE_DIMACS_BYTES", len(cnf))
    proof_record = proof._physical_record(
        drat, tmp_path, "binary-drat", cap=1,
    )
    check, stdout, stderr, bound = proof._run_checker(
        target=tmp_path,
        role="drat-verify",
        checker_path=proof.DRAT_TRIM_PATH,
        checker_sha256=proof.EXPECTED_DRAT_TRIM_SHA256,
        proof_path=drat,
        proof_record=proof_record,
        proof_cap=1,
        marker=b"s VERIFIED",
    )
    assert check["verified"] is True
    assert stderr == b""
    assert bound == proof_record
    invocation = check["invocation"]
    assert invocation["dynamic_runtime"]["loader_options"] == [
        "--inhibit-cache", "--library-path", "--argv0",
    ]
    assert invocation["argv_roles"][:6] == [
        "sealed-loader-memfd", "--inhibit-cache", "--library-path",
        "private-runtime-dirfd", "--argv0", "drat-verify",
    ]
    assert check["process"]["argv"][1] == "--inhibit-cache"
    assert b"s VERIFIED" in stdout


def test_exact_checker_validator_rejects_resealed_mutations(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    (tmp_path / "static").mkdir()
    cnf = b"p cnf 1 2\n1 0\n-1 0\n"
    (tmp_path / proof.STATIC_DIMACS).write_bytes(cnf)
    drat = tmp_path / "toy.drat"
    drat.write_bytes(b"")
    monkeypatch.setattr(
        proof, "EXPECTED_BASE_DIMACS_SHA256", hashlib.sha256(cnf).hexdigest(),
    )
    monkeypatch.setattr(proof, "EXPECTED_BASE_DIMACS_BYTES", len(cnf))
    proof_record = proof._physical_record(
        drat, tmp_path, "binary-drat", cap=1,
    )
    check, stdout, stderr, _bound = proof._run_checker(
        target=tmp_path,
        role="drat-verify",
        checker_path=proof.DRAT_TRIM_PATH,
        checker_sha256=proof.EXPECTED_DRAT_TRIM_SHA256,
        proof_path=drat,
        proof_record=proof_record,
        proof_cap=1,
        marker=b"s VERIFIED",
    )
    source_tcb = proof._dynamic_elf_tcb_binding()

    def valid(value: dict, out: bytes = stdout) -> bool:
        return proof._validate_checker_record(
            value,
            stdout=out,
            stderr=stderr,
            expected_role="drat-verify",
            marker=b"s VERIFIED",
            expected_checker_sha256=proof.EXPECTED_DRAT_TRIM_SHA256,
            target=tmp_path,
            expected_proof_record=proof_record,
            proof_cap=1,
            expected_output_role=None,
            source_tcb=source_tcb,
        )

    assert valid(check)
    wrong_role = json.loads(json.dumps(check))
    wrong_role["invocation"]["output_role"] = "lrat"
    wrong_role["invocation"] = proof.seal(wrong_role["invocation"])
    wrong_role = proof.seal(wrong_role)
    assert not valid(wrong_role)

    bool_rc = json.loads(json.dumps(check))
    bool_rc["process"]["exit_code"] = False
    bool_rc["process"] = proof.seal(bool_rc["process"])
    bool_rc = proof.seal(bool_rc)
    assert not valid(bool_rc)

    bool_schema = json.loads(json.dumps(check))
    bool_schema["schema_version"] = True
    bool_schema = proof.seal(bool_schema)
    assert not valid(bool_schema)

    float_timeout = json.loads(json.dumps(check))
    float_timeout["invocation"]["timeout_s"] = float(proof.CHECKER_TIMEOUT_S)
    float_timeout["invocation"] = proof.seal(float_timeout["invocation"])
    float_timeout = proof.seal(float_timeout)
    assert not valid(float_timeout)

    noncanonical_fd = json.loads(json.dumps(check))
    original_fd = noncanonical_fd["process"]["argv"][0]
    fd_number = int(original_fd.rsplit("/", 1)[1])
    noncanonical_fd["process"]["argv"][0] = f"/proc/self/fd/000{fd_number}"
    noncanonical_fd["invocation"]["actual_argv_sha256"] = proof.canonical_sha256(
        noncanonical_fd["process"]["argv"],
    )
    noncanonical_fd["invocation"] = proof.seal(noncanonical_fd["invocation"])
    noncanonical_fd["process"] = proof.seal(noncanonical_fd["process"])
    noncanonical_fd = proof.seal(noncanonical_fd)
    assert not valid(noncanonical_fd)

    conflict = stdout + b"s NOT VERIFIED\n"
    conflict_record = json.loads(json.dumps(check))
    conflict_record["process"]["stdout"] = proof._hash_record(conflict)
    conflict_record["process"] = proof.seal(conflict_record["process"])
    conflict_record["semantic_marker_count"] = 1
    conflict_record = proof.seal(conflict_record)
    assert not valid(conflict_record, conflict)


def test_fresh_checker_validator_rejects_float_invocation_cap(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    (tmp_path / "static").mkdir()
    cnf = b"p cnf 1 2\n1 0\n-1 0\n"
    (tmp_path / proof.STATIC_DIMACS).write_bytes(cnf)
    drat = tmp_path / "toy.drat"
    drat.write_bytes(b"")
    monkeypatch.setattr(
        proof, "EXPECTED_BASE_DIMACS_SHA256", hashlib.sha256(cnf).hexdigest(),
    )
    monkeypatch.setattr(proof, "EXPECTED_BASE_DIMACS_BYTES", len(cnf))
    proof_record = proof._physical_record(
        drat, tmp_path, "binary-drat", cap=1,
    )
    check, stdout, stderr, _bound = proof._run_checker(
        target=tmp_path,
        role="final-drat-replay",
        checker_path=proof.DRAT_TRIM_PATH,
        checker_sha256=proof.EXPECTED_DRAT_TRIM_SHA256,
        proof_path=drat,
        proof_record=proof_record,
        proof_cap=1,
        marker=b"s VERIFIED",
    )
    source_tcb = proof._dynamic_elf_tcb_binding()

    def validate(value: dict) -> None:
        proof._validate_fresh_checker_binding(
            value,
            role="final-drat-replay",
            marker=b"s VERIFIED",
            checker_path=proof.DRAT_TRIM_PATH,
            checker_sha256=proof.EXPECTED_DRAT_TRIM_SHA256,
            checker_bytes=proof.EXPECTED_DRAT_TRIM_BYTES,
            proof_record=proof_record,
            proof_cap=1,
            stdout_record=value["process"]["stdout"],
            stderr_record=value["process"]["stderr"],
            stdout_payload=stdout,
            stderr_payload=stderr,
            target=tmp_path,
            source_tcb=source_tcb,
        )

    validate(check)
    changed = json.loads(json.dumps(check))
    changed["invocation"]["stdout_cap_bytes"] = float(
        proof.CHECKER_LOG_MAX_BYTES,
    )
    changed["invocation"] = proof.seal(changed["invocation"])
    changed = proof.seal(changed)
    with pytest.raises(proof.ProofRunnerError, match="invocation binding"):
        validate(changed)


def test_rename_linearization_precedes_parent_fsync_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = tmp_path / "source"
    source.mkdir(mode=0o700)
    (source / "bound").write_bytes(b"proof")
    parent_fd = os.open(
        tmp_path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
    )
    try:
        destination = proof._create_empty_directory_at(parent_fd, "destination")
        state = {"location": "QUARANTINED_DURABLE"}

        def fail_fsync(_descriptor: int) -> None:
            raise OSError("injected parent fsync failure")

        monkeypatch.setattr(proof.os, "fsync", fail_fsync)
        with pytest.raises(OSError, match="injected parent fsync failure"):
            proof._replace_empty_directory_at(
                parent_fd,
                "source",
                "destination",
                expected_destination=destination,
                transition_state=state,
                transition_value="PUBLISHED_UNDURABLE",
            )
        assert state == {"location": "PUBLISHED_UNDURABLE"}
        assert not source.exists()
        assert (tmp_path / "destination" / "bound").read_bytes() == b"proof"
    finally:
        os.close(parent_fd)


def test_solver_invocation_rejects_numeric_aliases(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(proof, "_validate_memfd_record", lambda *args, **kwargs: True)
    monkeypatch.setattr(
        proof, "_validate_historical_dynamic_runtime",
        lambda *args, **kwargs: True,
    )
    monkeypatch.setattr(proof, "_validate_process_record", lambda value: True)
    argv = [
        "/proc/self/fd/3", "--inhibit-cache", "--library-path",
        "/proc/self/fd/4", "--argv0", "cadical-rel-1.9.5",
        "/proc/self/fd/5", "-q", "-t", str(proof.SOLVER_TIMEOUT_S),
        "/proc/self/fd/6", "/proc/self/fd/7",
    ]
    environment = proof._clean_env()
    invocation = proof.seal({
        "schema_version": proof.SCHEMA_VERSION,
        "kind": "paper400-standalone-solver-invocation-v2",
        "argv_roles": [
            "sealed-loader-memfd", "--inhibit-cache", "--library-path",
            "private-runtime-dirfd", "--argv0", "cadical-rel-1.9.5",
            "sealed-cadical195-memfd", "-q", "-t", "43200",
            "sealed-base-dimacs-memfd", "private-o_excl-binary-drat-fd",
        ],
        "actual_argv_sha256": proof.canonical_sha256(argv),
        "dynamic_runtime": {"library_path": "/proc/self/fd/4"},
        "solver": {},
        "base": {},
        "proof_format": "binary-drat-default",
        "solver_timeout_s": proof.SOLVER_TIMEOUT_S,
        "workers": 1,
        "resume": False,
        "stdin": "DEVNULL",
        "stdout_cap_bytes": proof.SOLVER_STDOUT_MAX_BYTES,
        "stderr_cap_bytes": proof.SOLVER_STDERR_MAX_BYTES,
        "proof_cap_bytes": proof.PROOF_MAX_BYTES,
        "environment": environment,
    })
    process = {
        "argv": argv,
        "cwd": str(tmp_path),
        "environment": environment,
        "timeout_s": proof.SOLVER_TIMEOUT_S,
        "stdout_cap_bytes": proof.SOLVER_STDOUT_MAX_BYTES,
        "stderr_cap_bytes": proof.SOLVER_STDERR_MAX_BYTES,
        "file_size_cap_bytes": proof.PROOF_MAX_BYTES,
    }

    def valid(value: dict) -> bool:
        return proof._validate_solver_invocation(
            value, process=process, target=tmp_path, source_tcb={},
        )

    assert valid(invocation)
    for field in ("workers", "proof_cap_bytes"):
        changed = json.loads(json.dumps(invocation))
        changed[field] = float(changed[field])
        changed = proof.seal(changed)
        assert not valid(changed)


def _valid_zero_cap_resource_record() -> dict:
    maximum = 256 << 30
    current = 8 << 30
    block_size = 4096
    available_blocks = ((proof.DISK_RESERVE_MARGIN_BYTES + block_size - 1) // block_size) + 1
    available_bytes = block_size * available_blocks
    return proof.seal({
        "schema_version": proof.SCHEMA_VERSION,
        "kind": "standalone-resource-gate-v2",
        "cpu": 0,
        "affinity": [0],
        "niceness": 19,
        "busy_percent": [0.0] * proof.RESOURCE_CPU_INTERVALS,
        "cpu_safe": True,
        "memory_current": current,
        "memory_max": maximum,
        "file_bytes": 0,
        "inactive_file_bytes": 0,
        "reclaimable_file_bytes": 0,
        "raw_headroom_bytes": maximum - current,
        "effective_current_bytes": current,
        "effective_headroom_bytes": maximum - current,
        "effective_current_fraction": current / maximum,
        "memory_events": {
            "low": 0, "high": 0, "max": 0,
            "oom": 0, "oom_kill": 0, "oom_group_kill": 0,
        },
        "memory_pressure": {
            "some": {"avg10": 0.0, "avg60": 0.0, "avg300": 0.0, "total": 0},
            "full": {"avg10": 0.0, "avg60": 0.0, "avg300": 0.0, "total": 0},
        },
        "memory_capacity_safe": True,
        "pressure_safe": True,
        "oom_safe": True,
        "filesystem_device": 1,
        "filesystem_block_size": block_size,
        "filesystem_bavail_blocks": available_blocks,
        "filesystem_bavail_bytes": available_bytes,
        "output_cap_bytes": 0,
        "reserve_margin_bytes": proof.DISK_RESERVE_MARGIN_BYTES,
        "disk_required_bytes": proof.DISK_RESERVE_MARGIN_BYTES,
        "disk_safe": True,
        "thread_environment": {name: "1" for name in proof.THREAD_ENV},
        "thread_environment_safe": True,
        "passed": True,
    })


def test_resource_validator_rejects_bool_float_alias_and_formula_reseal() -> None:
    record = _valid_zero_cap_resource_record()
    assert proof._validate_resource_record(record, required_cap=0)
    for replacement in (False, 0.0):
        changed = json.loads(json.dumps(record))
        changed["output_cap_bytes"] = replacement
        changed = proof.seal(changed)
        assert not proof._validate_resource_record(changed, required_cap=0)
    changed = json.loads(json.dumps(record))
    for field in ("raw_headroom_bytes", "effective_headroom_bytes"):
        changed = json.loads(json.dumps(record))
        changed[field] = float(changed[field])
        changed = proof.seal(changed)
        assert not proof._validate_resource_record(changed, required_cap=0)
    changed["schema_version"] = True
    changed = proof.seal(changed)
    assert not proof._validate_resource_record(changed, required_cap=0)
    changed = json.loads(json.dumps(record))
    changed["filesystem_bavail_bytes"] += 1
    changed = proof.seal(changed)
    assert not proof._validate_resource_record(changed, required_cap=0)

def _resource_record_with_raw_headroom(raw_headroom: int) -> dict:
    record = json.loads(json.dumps(_valid_zero_cap_resource_record()))
    record.pop("record_sha256")
    maximum = 256 << 30
    current = maximum - raw_headroom
    reclaimable = 65 << 30
    effective_current = current - reclaimable
    effective_headroom = maximum - effective_current
    memory_safe = bool(
        raw_headroom >= proof.RESOURCE_MIN_RAW_HEADROOM
        and effective_headroom >= proof.RESOURCE_MIN_EFFECTIVE_HEADROOM
        and effective_current / maximum <= proof.RESOURCE_MAX_EFFECTIVE_FRACTION
    )
    record.update({
        "memory_current": current,
        "memory_max": maximum,
        "file_bytes": reclaimable,
        "inactive_file_bytes": reclaimable,
        "reclaimable_file_bytes": reclaimable,
        "raw_headroom_bytes": raw_headroom,
        "effective_current_bytes": effective_current,
        "effective_headroom_bytes": effective_headroom,
        "effective_current_fraction": effective_current / maximum,
        "memory_capacity_safe": memory_safe,
        "passed": memory_safe,
    })
    return proof.seal(record)


def test_no_raw_admission_boundary_is_exact_and_replayable() -> None:
    at_floor = _resource_record_with_raw_headroom(0)
    below_floor = _resource_record_with_raw_headroom(-1)
    assert proof._validate_resource_record(at_floor, required_cap=0)
    assert at_floor["passed"] is True
    assert not proof._validate_resource_record(below_floor, required_cap=0)
    assert below_floor["passed"] is False



def test_test_only_raw_cannot_reach_checker(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = tmp_path / "result"
    root.mkdir(mode=0o700)
    monkeypatch.setattr(
        proof, "_validate_root_argument",
        lambda value, must_exist: Path(value),
    )
    monkeypatch.setattr(
        proof, "_require_production_cli",
        lambda action, target, nonce: {"passed": True},
    )
    monkeypatch.setattr(
        proof, "_validate_raw",
        lambda target, fresh_source_and_tools: {
            "static": {"authority": proof.AUTHORITY_TEST_ONLY, "test_only": True},
            "raw": {
                "authority": proof.AUTHORITY_TEST_ONLY,
                "test_only": True,
                "production_eligible": True,
            },
            "state": "RAW_UNSAT",
            "strict_raw_unsat": True,
        },
    )
    checker_calls = []
    monkeypatch.setattr(
        proof, "_run_checker",
        lambda **kwargs: checker_calls.append(kwargs),
    )
    with pytest.raises(proof.ProofRunnerError, match="tainted RAW"):
        proof.verify_root(root)
    assert checker_calls == []
    assert not (root / proof.VERIFY_CLAIM).exists()


def test_static_builder_fixed_fields_cannot_survive_deep_reconstruction(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    identity = {
        "absolute_path": str(tmp_path),
        "device": 1,
        "inode": 2,
        "mode": 0o700,
        "uid": os.geteuid(),
    }
    monkeypatch.setattr(proof, "_root_identity", lambda _root: identity)
    context = {"direct": "prepare"}
    summary = {"summary": "sealed"}
    old_record = {"role": "old"}
    base_record = {"role": "base"}
    canonical = proof._static_manifest(
        tmp_path, context, summary, old_record, base_record,
        authority=proof.AUTHORITY_PRODUCTION,
    )
    assert canonical["base"]["maximum_excluded_weight"] == 18
    for mutate in (
        lambda value: value["base"].__setitem__("maximum_excluded_weight", 17),
        lambda value: value.__setitem__("schema_version", True),
        lambda value: value.__setitem__("direct_cli_context", {"passed": False}),
    ):
        changed = json.loads(json.dumps(canonical))
        mutate(changed)
        changed = proof.seal(changed)
        rebuilt = proof._static_manifest(
            tmp_path, context, summary, old_record, base_record,
            authority=proof.AUTHORITY_PRODUCTION,
        )
        assert not proof.json_type_equal(changed, rebuilt)
    source = SOURCE.read_text(encoding="utf-8")
    static_validator = source.split("def _validate_static(", 1)[1].split(
        "def preflight_only", 1,
    )[0]
    assert "json_type_equal(manifest, expected_manifest)" in static_validator
    assert "_validate_stored_direct_cli_context(" in static_validator

@pytest.mark.parametrize(
    ("action", "function_name", "result", "expected_rc"),
    [
        ("solve", "solve_root", {"state": "UNRESOLVED"}, 2),
        ("solve", "solve_root", {}, 2),
        ("solve", "solve_root", {"state": "BROKEN"}, 2),
        ("solve", "solve_root", {"state": "RAW_SAT"}, 0),
        ("solve", "solve_root", {"state": "RAW_UNSAT"}, 0),
        ("verify", "verify_root", {"state": "UNRESOLVED"}, 2),
        ("verify", "verify_root", {"state": "LRAT_VERIFIED"}, 0),
        ("validate", "validate_final_root", {"valid": False}, 2),
        ("validate", "validate_final_root", {"valid": True}, 0),
    ],
)
def test_cli_exit_code_is_fail_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capfd: pytest.CaptureFixture[str],
    action: str,
    function_name: str,
    result: dict,
    expected_rc: int,
) -> None:
    monkeypatch.setattr(
        proof, function_name, lambda *args, **kwargs: dict(result),
    )
    rc = proof.main([action, "--root", str(tmp_path / "result")])
    assert rc == expected_rc
    assert json.loads(capfd.readouterr().out) == result


def test_resource_snapshot_pressure_is_exactly_typed() -> None:
    pressure_record = {
        "avg10": 0.0,
        "avg60": 0.0,
        "avg300": 0.0,
        "total": 0,
    }
    snapshot = {
        "memory_current": 0,
        "memory_max": 1,
        "memory_stat": {},
        "memory_events": {},
        "memory_pressure": {
            "some": dict(pressure_record),
            "full": dict(pressure_record),
        },
        "filesystem_device": 1,
        "filesystem_block_size": 4096,
        "filesystem_bavail_blocks": 1,
        "filesystem_bavail_bytes": 4096,
    }
    assert proof._validate_resource_snapshot(snapshot)
    mutations = []
    missing_pressure = json.loads(json.dumps(snapshot))
    missing_pressure["memory_pressure"] = {}
    mutations.append(missing_pressure)
    float_total = json.loads(json.dumps(snapshot))
    float_total["memory_pressure"]["some"]["total"] = 0.0
    mutations.append(float_total)
    integer_average = json.loads(json.dumps(snapshot))
    integer_average["memory_pressure"]["full"]["avg10"] = 0
    mutations.append(integer_average)
    nonfinite_average = json.loads(json.dumps(snapshot))
    nonfinite_average["memory_pressure"]["full"]["avg60"] = float("inf")
    mutations.append(nonfinite_average)
    extra_field = json.loads(json.dumps(snapshot))
    extra_field["memory_pressure"]["some"]["extra"] = 0.0
    mutations.append(extra_field)
    assert all(not proof._validate_resource_snapshot(value) for value in mutations)


def _wait_until(predicate, *, timeout_s: float = 8.0) -> bool:
    deadline = time.monotonic() + timeout_s
    while time.monotonic() < deadline:
        if predicate():
            return True
        time.sleep(0.05)
    return predicate()


def _pid_not_running(pid: int) -> bool:
    try:
        fields = Path(f"/proc/{pid}/stat").read_text(encoding="ascii").split()
    except (FileNotFoundError, ProcessLookupError):
        return True
    return len(fields) >= 3 and fields[2] == "Z"


def _group_absent(pgid: int) -> bool:
    try:
        os.killpg(pgid, 0)
        return False
    except ProcessLookupError:
        return True


def _controller_script(child_script: Path, child_cwd: Path) -> str:
    return (
        "import importlib.util,pathlib,sys\n"
        f"source=pathlib.Path({str(SOURCE)!r})\n"
        "spec=importlib.util.spec_from_file_location('proof_v2_controller',source)\n"
        "module=importlib.util.module_from_spec(spec)\n"
        "spec.loader.exec_module(module)\n"
        "try:\n"
        " module._run_capped_process(\n"
        f"  [sys.executable,'-I','-B',{str(child_script)!r}],\n"
        "  timeout_s=60,stdout_cap=4096,stderr_cap=4096,\n"
        f"  cwd=pathlib.Path({str(child_cwd)!r}),file_size_cap=4096)\n"
        "except module._ForwardedParentSignal as exc:\n"
        " module._terminate_by_forwarded_signal(exc.signum)\n"
        "raise SystemExit(97)\n"
    )


@pytest.mark.parametrize(
    "signum", [int(signal.SIGHUP), int(signal.SIGINT), int(signal.SIGTERM)],
)
def test_parent_signal_is_forwarded_to_child_pgid_then_reraised(
    tmp_path: Path, signum: int,
) -> None:
    ready = tmp_path / "ready"
    observed = tmp_path / "observed"
    fake = tmp_path / "signal_child.py"
    fake.write_text(
        "import os,signal,time\n"
        f"ready={str(ready)!r}\n"
        f"observed={str(observed)!r}\n"
        "def handle(signum,_frame):\n"
        " fd=os.open(observed,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600)\n"
        " try:\n"
        "  os.write(fd,(str(signum)+' '+str(os.getpid())+' '+str(os.getpgrp())).encode())\n"
        "  os.fsync(fd)\n"
        " finally:\n"
        "  os.close(fd)\n"
        " os._exit(0)\n"
        "for item in (signal.SIGHUP,signal.SIGINT,signal.SIGTERM):\n"
        " signal.signal(item,handle)\n"
        "fd=os.open(ready,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)\n"
        "os.write(fd,(str(os.getpid())+' '+str(os.getpgrp())).encode())\n"
        "os.fsync(fd);os.close(fd)\n"
        "while True: time.sleep(1)\n",
        encoding="utf-8",
    )
    controller = subprocess.Popen(
        [sys.executable, "-I", "-B", "-c", _controller_script(fake, tmp_path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    child_pid = child_pgid = None
    try:
        assert _wait_until(ready.exists)
        child_pid, child_pgid = map(int, ready.read_text().split())
        os.kill(controller.pid, signum)
        _stdout, stderr = controller.communicate(timeout=12)
        assert controller.returncode == -signum, stderr
        assert _wait_until(observed.exists)
        observed_signal, observed_pid, observed_pgid = map(
            int, observed.read_text().split(),
        )
        assert (observed_signal, observed_pid, observed_pgid) == (
            signum, child_pid, child_pgid,
        )
        assert _wait_until(lambda: _pid_not_running(child_pid))
        assert _wait_until(lambda: _group_absent(child_pgid))
    finally:
        if controller.poll() is None:
            os.killpg(controller.pid, signal.SIGKILL)
            controller.wait(timeout=5)
        if child_pgid is not None and not _group_absent(child_pgid):
            os.killpg(child_pgid, signal.SIGKILL)


def test_controller_sigkill_triggers_child_pdeathsig(tmp_path: Path) -> None:
    ready = tmp_path / "pdeath-ready"
    fake = tmp_path / "pdeath_child.py"
    fake.write_text(
        "import os,time\n"
        f"ready={str(ready)!r}\n"
        "fd=os.open(ready,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)\n"
        "os.write(fd,(str(os.getpid())+' '+str(os.getpgrp())).encode())\n"
        "os.fsync(fd);os.close(fd)\n"
        "while True: time.sleep(1)\n",
        encoding="utf-8",
    )
    controller = subprocess.Popen(
        [sys.executable, "-I", "-B", "-c", _controller_script(fake, tmp_path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    child_pid = child_pgid = None
    try:
        assert _wait_until(ready.exists)
        child_pid, child_pgid = map(int, ready.read_text().split())
        os.kill(controller.pid, signal.SIGKILL)
        controller.communicate(timeout=8)
        assert controller.returncode == -signal.SIGKILL
        assert _wait_until(lambda: _pid_not_running(child_pid))
    finally:
        if controller.poll() is None:
            os.killpg(controller.pid, signal.SIGKILL)
            controller.wait(timeout=5)
        if child_pgid is not None and not _group_absent(child_pgid):
            os.killpg(child_pgid, signal.SIGKILL)


def test_timeout_kills_same_pgid_fork_and_confirms_empty(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    ready = tmp_path / "fork-ready"
    fake = tmp_path / "fork_child.py"
    fake.write_text(
        "import os,signal,time\n"
        f"ready={str(ready)!r}\n"
        "descendant=os.fork()\n"
        "if descendant==0:\n"
        " while True: time.sleep(1)\n"
        "signal.signal(signal.SIGTERM,signal.SIG_IGN)\n"
        "fd=os.open(ready,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)\n"
        "os.write(fd,(str(os.getpid())+' '+str(descendant)+' '+str(os.getpgrp())).encode())\n"
        "os.fsync(fd);os.close(fd)\n"
        "while True: time.sleep(1)\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(proof, "TERM_GRACE_S", 1)
    result, stdout, _stderr = proof._run_capped_process(
        [sys.executable, "-I", "-B", str(fake)],
        timeout_s=1,
        stdout_cap=1024,
        stderr_cap=1024,
        cwd=tmp_path,
        file_size_cap=1024,
    )
    leader, descendant, pgid = map(int, ready.read_text().split())
    assert result["timed_out"] is True
    assert result["direct_child_reaped"] is True
    assert result["process_group_empty"] is True
    assert result["pdeathsig_setup_confirmed"] is True
    assert result["session_setup_confirmed"] is True
    assert proof._validate_process_record(result)
    assert not proof._process_clean(result, rc=0)
    assert _wait_until(lambda: _pid_not_running(leader))
    assert _wait_until(lambda: _pid_not_running(descendant))
    assert _wait_until(lambda: _group_absent(pgid))


def test_prctl_failure_is_fail_closed_before_exec(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(proof, "_PRCTL", lambda *_args: -1)
    result, stdout, stderr = proof._run_capped_process(
        [sys.executable, "-I", "-B", "-c", "print('must-not-run')"],
        timeout_s=5,
        stdout_cap=1024,
        stderr_cap=1024,
        cwd=tmp_path,
        file_size_cap=1024,
    )
    assert result["child_pid"] is None
    assert result["pdeathsig_setup_confirmed"] is False
    assert result["session_setup_confirmed"] is False
    assert result["direct_child_reaped"] is False
    assert result["process_group_empty"] is True
    assert result["launch_error"] is not None
    assert stdout == stderr == b""
    assert proof._validate_process_record(result)
    assert not proof._process_clean(result, rc=0)


def test_pdeathsig_parent_race_check_self_kills_child() -> None:
    child = os.fork()
    if child == 0:
        proof._child_setup(1024, os.getppid() + 100_000)
        os._exit(99)
    waited, status = os.waitpid(child, 0)
    assert waited == child
    assert os.WIFSIGNALED(status)
    assert os.WTERMSIG(status) == signal.SIGKILL


def test_process_record_lifecycle_mutations_are_rejected(tmp_path: Path) -> None:
    result, stdout, _stderr = proof._run_capped_process(
        [
            sys.executable, "-I", "-B", "-c",
            "import os; print(os.getpid(), os.getpgrp(), os.getsid(0))",
        ],
        timeout_s=5,
        stdout_cap=1024,
        stderr_cap=1024,
        cwd=tmp_path,
        file_size_cap=1024,
    )
    observed_pid, observed_pgid, observed_sid = map(int, stdout.split())
    assert (observed_pid, observed_pgid, observed_sid) == (
        result["child_pid"], result["process_group_id"], result["child_pid"],
    )
    assert proof._validate_process_record(result)
    assert proof._process_clean(result, rc=0)
    mutations = []
    no_pdeath = json.loads(json.dumps(result))
    no_pdeath["pdeathsig_setup_confirmed"] = False
    no_pdeath["session_setup_confirmed"] = False
    mutations.append(no_pdeath)
    group_not_empty = json.loads(json.dumps(result))
    group_not_empty["process_group_empty"] = False
    mutations.append(group_not_empty)
    weak_policy = json.loads(json.dumps(result))
    weak_policy["child_lifecycle_policy"]["forwarded_parent_signals"] = []
    mutations.append(weak_policy)
    for changed in mutations:
        changed = proof.seal(changed)
        assert not proof._validate_process_record(changed)
        assert not proof._process_clean(changed, rc=0)


def _assert_clean_supervised_record(record: dict, *, rc: int) -> None:
    assert record["pdeathsig_setup_confirmed"] is True
    assert record["session_setup_confirmed"] is True
    assert record["direct_child_reaped"] is True
    assert record["process_group_empty"] is True
    assert record["child_pid"] == record["process_group_id"]
    assert proof._validate_process_record(record)
    assert proof._process_clean(record, rc=rc)


def test_selector_exception_cleanup_failure_has_priority_and_restores_handlers(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    ready = tmp_path / "selector-ready"
    fake = tmp_path / "selector_child.py"
    fake.write_text(
        "import os,time\n"
        f"ready={str(ready)!r}\n"
        "descendant=os.fork()\n"
        "if descendant==0:\n"
        " os.close(1);os.close(2)\n"
        " while True: time.sleep(1)\n"
        "fd=os.open(ready,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)\n"
        "os.write(fd,(str(os.getpid())+' '+str(descendant)+' '+str(os.getpgrp())).encode())\n"
        "os.fsync(fd);os.close(fd)\n"
        "while True: time.sleep(1)\n",
        encoding="utf-8",
    )
    real_selector = proof.selectors.DefaultSelector

    class TrapSelector:
        def __init__(self) -> None:
            self.inner = real_selector()

        def __getattr__(self, name):
            return getattr(self.inner, name)

        def select(self, timeout=None):
            if ready.exists():
                raise RuntimeError("selector trap")
            return self.inner.select(timeout)

    previous = {
        signum: signal.getsignal(signum)
        for signum in proof.FORWARDED_PARENT_SIGNALS
    }
    monkeypatch.setattr(proof.selectors, "DefaultSelector", TrapSelector)
    monkeypatch.setattr(proof, "TERM_GRACE_S", 0)
    monkeypatch.setattr(proof, "_group_exists", lambda _pid: True)
    ids = None
    caught = None
    try:
        with pytest.raises(proof.ProofRunnerError, match="cleanup did not confirm") as caught:
            proof._run_capped_process(
                [sys.executable, "-I", "-B", str(fake)],
                timeout_s=5, stdout_cap=1024, stderr_cap=1024,
                cwd=tmp_path, file_size_cap=1024,
            )
        assert isinstance(caught.value.__cause__, RuntimeError)
        assert str(caught.value.__cause__) == "selector trap"
        ids = tuple(map(int, ready.read_text().split()))
        assert all(
            signal.getsignal(signum) is previous[signum]
            for signum in proof.FORWARDED_PARENT_SIGNALS
        )
    finally:
        monkeypatch.undo()
        if ids is not None and not _group_absent(ids[2]):
            os.killpg(ids[2], signal.SIGKILL)
    assert ids is not None
    assert _wait_until(lambda: _pid_not_running(ids[0]))
    assert _wait_until(lambda: _pid_not_running(ids[1]))
    assert _wait_until(lambda: _group_absent(ids[2]))


def test_natural_leader_exit_cleans_lingering_same_pgid_descendant(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    ready = tmp_path / "natural-ready"
    fake = tmp_path / "natural_child.py"
    fake.write_text(
        "import os,time\n"
        f"ready={str(ready)!r}\n"
        "descendant=os.fork()\n"
        "if descendant==0:\n"
        " os.close(1);os.close(2)\n"
        " while True: time.sleep(1)\n"
        "fd=os.open(ready,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)\n"
        "os.write(fd,(str(os.getpid())+' '+str(descendant)+' '+str(os.getpgrp())).encode())\n"
        "os.fsync(fd);os.close(fd)\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(proof, "TERM_GRACE_S", 2)
    result, stdout, stderr = proof._run_capped_process(
        [sys.executable, "-I", "-B", str(fake)],
        timeout_s=5, stdout_cap=1024, stderr_cap=1024,
        cwd=tmp_path, file_size_cap=1024,
    )
    leader, descendant, pgid = map(int, ready.read_text().split())
    try:
        assert stdout == stderr == b""
        assert result["exit_code"] == 0
        assert result["timed_out"] is False
        assert result["lingering_process_group"] is True
        assert result["direct_child_reaped"] is True
        assert result["process_group_empty"] is True
        assert proof._validate_process_record(result)
        assert not proof._process_clean(result, rc=0)
        assert _wait_until(lambda: _pid_not_running(leader))
        assert _wait_until(lambda: _pid_not_running(descendant))
        assert _wait_until(lambda: _group_absent(pgid))
    finally:
        if not _group_absent(pgid):
            os.killpg(pgid, signal.SIGKILL)


def test_signal_pending_before_popen_return_is_forwarded_after_pid_assignment(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    ready = tmp_path / "pending-ready"
    observed = tmp_path / "pending-observed"
    fake = tmp_path / "pending_child.py"
    fake.write_text(
        "import os,signal,time\n"
        f"ready={str(ready)!r}\n"
        f"observed={str(observed)!r}\n"
        "def handle(signum,_frame):\n"
        " fd=os.open(observed,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)\n"
        " os.write(fd,(str(signum)+' '+str(os.getpid())+' '+str(os.getpgrp())).encode())\n"
        " os.fsync(fd);os.close(fd);os._exit(0)\n"
        "signal.signal(signal.SIGTERM,handle)\n"
        "fd=os.open(ready,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)\n"
        "os.write(fd,(str(os.getpid())+' '+str(os.getpgrp())).encode())\n"
        "os.fsync(fd);os.close(fd)\n"
        "while True: time.sleep(1)\n",
        encoding="utf-8",
    )
    real_popen = proof.subprocess.Popen

    def delayed_return(*args, **kwargs):
        process = real_popen(*args, **kwargs)
        deadline = time.monotonic() + 4
        while not ready.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        os.kill(os.getpid(), signal.SIGTERM)
        return process

    previous = {
        signum: signal.getsignal(signum)
        for signum in proof.FORWARDED_PARENT_SIGNALS
    }
    monkeypatch.setattr(proof.subprocess, "Popen", delayed_return)
    child_pid = child_pgid = None
    try:
        with pytest.raises(proof._ForwardedParentSignal) as caught:
            proof._run_capped_process(
                [sys.executable, "-I", "-B", str(fake)],
                timeout_s=8, stdout_cap=1024, stderr_cap=1024,
                cwd=tmp_path, file_size_cap=1024,
            )
        assert caught.value.signum == signal.SIGTERM
        child_pid, child_pgid = map(int, ready.read_text().split())
        assert _wait_until(observed.exists)
        assert tuple(map(int, observed.read_text().split())) == (
            signal.SIGTERM, child_pid, child_pgid,
        )
        assert all(
            signal.getsignal(signum) is previous[signum]
            for signum in proof.FORWARDED_PARENT_SIGNALS
        )
        assert _wait_until(lambda: _pid_not_running(child_pid))
        assert _wait_until(lambda: _group_absent(child_pgid))
    finally:
        if child_pgid is not None and not _group_absent(child_pgid):
            os.killpg(child_pgid, signal.SIGKILL)


def test_gnu_timeout_outer_term_leaves_no_child_group(tmp_path: Path) -> None:
    ready = tmp_path / "outer-ready"
    fake = tmp_path / "outer_child.py"
    fake.write_text(
        "import os,time\n"
        f"ready={str(ready)!r}\n"
        "fd=os.open(ready,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)\n"
        "os.write(fd,(str(os.getpid())+' '+str(os.getpgrp())).encode())\n"
        "os.fsync(fd);os.close(fd)\n"
        "while True: time.sleep(1)\n",
        encoding="utf-8",
    )
    completed = subprocess.run(
        [
            "/usr/bin/timeout", "--signal=TERM", "--kill-after=4s", "2s",
            sys.executable, "-I", "-B", "-c", _controller_script(fake, tmp_path),
        ],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        timeout=10, check=False,
    )
    assert completed.returncode == 124, completed.stderr
    assert ready.exists()
    child_pid, child_pgid = map(int, ready.read_text().split())
    try:
        assert _wait_until(lambda: _pid_not_running(child_pid))
        assert _wait_until(lambda: _group_absent(child_pgid))
    finally:
        if not _group_absent(child_pgid):
            os.killpg(child_pgid, signal.SIGKILL)


def test_root_is_confined_to_direct_child_of_project_results(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    project = tmp_path / "project"
    results = project / "results"
    results.mkdir(parents=True, mode=0o700)
    monkeypatch.setattr(proof, "PROJECT", project)
    target = results / "production-run"
    assert proof._validate_root_argument(target, must_exist=False) == target
    target.mkdir(mode=0o700)
    assert proof._validate_root_argument(target, must_exist=True) == target
    for rejected in (
        project / "production-run",
        results / "nested" / "production-run",
        tmp_path / "production-run",
    ):
        with pytest.raises(proof.ProofRunnerError, match="direct child"):
            proof._validate_root_argument(rejected, must_exist=False)


def test_selector_exception_reaps_real_group_before_propagating_original(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    ready = tmp_path / "selector-clean-ready"
    fake = tmp_path / "selector_clean_child.py"
    fake.write_text(
        "import os,time\n"
        f"ready={str(ready)!r}\n"
        "descendant=os.fork()\n"
        "if descendant==0:\n"
        " os.close(1);os.close(2)\n"
        " while True: time.sleep(1)\n"
        "fd=os.open(ready,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)\n"
        "os.write(fd,(str(os.getpid())+' '+str(descendant)+' '+str(os.getpgrp())).encode())\n"
        "os.fsync(fd);os.close(fd)\n"
        "while True: time.sleep(1)\n",
        encoding="utf-8",
    )
    real_selector = proof.selectors.DefaultSelector

    class TrapSelector:
        def __init__(self) -> None:
            self.inner = real_selector()

        def __getattr__(self, name):
            return getattr(self.inner, name)

        def select(self, timeout=None):
            if ready.exists():
                raise RuntimeError("clean selector trap")
            return self.inner.select(timeout)

    previous = {
        signum: signal.getsignal(signum)
        for signum in proof.FORWARDED_PARENT_SIGNALS
    }
    monkeypatch.setattr(proof.selectors, "DefaultSelector", TrapSelector)
    monkeypatch.setattr(proof, "TERM_GRACE_S", 2)
    ids = None
    try:
        with pytest.raises(RuntimeError, match="clean selector trap"):
            proof._run_capped_process(
                [sys.executable, "-I", "-B", str(fake)],
                timeout_s=5, stdout_cap=1024, stderr_cap=1024,
                cwd=tmp_path, file_size_cap=1024,
            )
        ids = tuple(map(int, ready.read_text().split()))
        assert _pid_not_running(ids[0])
        assert _pid_not_running(ids[1])
        assert _group_absent(ids[2])
        assert all(
            signal.getsignal(signum) is previous[signum]
            for signum in proof.FORWARDED_PARENT_SIGNALS
        )
    finally:
        if ids is not None and not _group_absent(ids[2]):
            os.killpg(ids[2], signal.SIGKILL)
