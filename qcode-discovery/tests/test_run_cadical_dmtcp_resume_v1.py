from __future__ import annotations

import hashlib
import importlib.util
import os
import stat
import sys
import time
from pathlib import Path

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "run_cadical_dmtcp_resume_v1.py"
)
SPEC = importlib.util.spec_from_file_location("cadical_dmtcp_resume_v1", SOURCE)
assert SPEC is not None and SPEC.loader is not None
resume_v1 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(resume_v1)


def _make_executable(path: Path, payload: bytes) -> None:
    path.write_bytes(payload)
    path.chmod(0o755)


def _fake_dmtcp_prefix(tmp_path: Path) -> Path:
    prefix = tmp_path / "dmtcp"
    bin_dir = prefix / "bin"
    lib_dir = prefix / "lib" / "dmtcp"
    bin_dir.mkdir(parents=True)
    lib_dir.mkdir(parents=True)
    for name in resume_v1.REQUIRED_DMTCP_BINS:
        # dmtcp_command 4.2.0 really exits 1 for --version; the other tools
        # exit zero.  Preserve that oddity in the fake toolchain.
        version_rc = 1 if name == "dmtcp_command" else 0
        script = (
            "#!/bin/sh\n"
            "if [ \"$1\" = \"--version\" ]; then\n"
            f"  echo '{name} (DMTCP) 4.2.0'\n"
            f"  exit {version_rc}\n"
            "fi\n"
            "exit 99\n"
        ).encode("ascii")
        _make_executable(bin_dir / name, script)
    (lib_dir / "libdmtcp.so").write_bytes(b"fake-dmtcp-library\n")
    return prefix


def _initialize_fake_root(tmp_path: Path) -> tuple[Path, Path]:
    prefix = _fake_dmtcp_prefix(tmp_path)
    solver = tmp_path / "solver"
    _make_executable(solver, b"#!/bin/sh\nexit 0\n")
    cnf = tmp_path / "input.cnf"
    cnf.write_bytes(b"p cnf 1 2\n1 0\n-1 0\n")
    root = tmp_path / "resume-root"
    resume_v1.initialize(
        root,
        cnf=cnf,
        solver=solver,
        dmtcp_prefix=prefix,
        solver_args=["-q"],
        runtime_libs=[],
        runtime_libs_complete=False,
    )
    return root, prefix


def test_manifest_is_canonical_self_hashed_and_duplicate_safe() -> None:
    doc = resume_v1.seal_manifest("unit", {"value": 1})
    payload = resume_v1.canonical_bytes(doc) + b"\n"
    assert resume_v1.decode_manifest(payload, expected_kind="unit") == doc
    assert resume_v1.selfhash_valid(doc)
    changed = dict(doc)
    changed["value"] = 2
    assert not resume_v1.selfhash_valid(changed)
    with pytest.raises(resume_v1.ResumeControllerError, match="duplicate"):
        resume_v1.decode_manifest(b'{"x":1,"x":1}\n')
    with pytest.raises(resume_v1.ResumeControllerError, match="canonical"):
        resume_v1.decode_manifest(b'{ "x":1}\n')


def test_init_binds_cnf_solver_dmtcp_bins_and_libraries(tmp_path: Path) -> None:
    root, _ = _initialize_fake_root(tmp_path)
    config = resume_v1.read_manifest(
        root / "00-init.commit.json", expected_kind="init.commit"
    )
    assert config["authority"] == "TEST_ONLY"
    assert config["dmtcp"]["version"] == "4.2.0"
    assert config["dmtcp"]["reference_commit"] == resume_v1.DMTCP_REFERENCE_COMMIT
    assert len(config["dmtcp"]["binaries"]) == len(
        resume_v1.REQUIRED_DMTCP_BINS
    )
    assert config["dmtcp"]["libraries"]
    report = resume_v1.inspect(root, verify_hashes=True)
    assert report["state"] == "INITIALIZED"


def test_bound_tool_mutation_fails_closed(tmp_path: Path) -> None:
    root, prefix = _initialize_fake_root(tmp_path)
    library = prefix / "lib" / "dmtcp" / "libdmtcp.so"
    library.write_bytes(b"changed\n")
    with pytest.raises(resume_v1.ResumeControllerError, match="binding mismatch"):
        resume_v1.inspect(root, verify_hashes=True)


def test_launch_and_restart_use_separate_generation_dirs_and_safe_flags(
    tmp_path: Path,
) -> None:
    binaries = {
        name: tmp_path / name for name in resume_v1.REQUIRED_DMTCP_BINS
    }
    gen0 = tmp_path / "generations" / "000000"
    gen1 = tmp_path / "generations" / "000001"
    image = gen0 / "images" / "ckpt_solver.dmtcp"
    launch = resume_v1._launch_argv(gen0, binaries, ["/solver", "in", "proof"])
    restart = resume_v1._restart_argv(gen1, binaries, [image])
    assert str(gen0 / "images") in launch
    assert str(gen1 / "images") in restart
    assert str(image) == restart[-1]
    for command in (launch, restart):
        assert not set(command).intersection(resume_v1.FORBIDDEN_DMTCP_TOKENS)
        assert "--ckptdir" in command
    with pytest.raises(resume_v1.ResumeControllerError, match="exactly one"):
        resume_v1._restart_argv(gen1, binaries, [])


def test_spawn_detached_fixes_dmtcp_artifact_umask(tmp_path: Path) -> None:
    artifact = tmp_path / "restart-script-mode"
    program = (
        "import os,sys,time; "
        "fd=os.open(sys.argv[1],os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o766); "
        "os.close(fd); time.sleep(60)"
    )
    pid, ticks = resume_v1._spawn_detached(
        [sys.executable, "-c", program, str(artifact)],
        cwd=tmp_path,
        stdout_path=tmp_path / "spawn.stdout",
        stderr_path=tmp_path / "spawn.stderr",
    )
    try:
        deadline = time.monotonic() + 5
        while not artifact.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        assert artifact.exists()
        assert stat.S_IMODE(artifact.stat().st_mode) == 0o744
    finally:
        resume_v1._kill_spawned_group(pid, ticks)


@pytest.mark.parametrize(
    ("returncode", "stdout", "stderr", "expected"),
    [
        (2, b"Computation was checkpointed and killed.\n", b"", True),
        (0, b"Computation was checkpointed and killed.\n", b"", True),
        (2, b"", b"", False),
        (2, b"Computation was checkpointed and killed.\nextra\n", b"", False),
        (2, b"Computation was checkpointed and killed.\n", b"warning\n", False),
        (1, b"Computation was checkpointed and killed.\n", b"", False),
    ],
)
def test_kcheckpoint_rc2_requires_exact_success_semantics(
    returncode: int, stdout: bytes, stderr: bytes, expected: bool
) -> None:
    assert resume_v1._kc_semantics(returncode, stdout, stderr) is expected


def test_uncommitted_tail_rejected_but_explicit_bound_tail_allowed(
    tmp_path: Path,
) -> None:
    root = tmp_path / "root"
    root.mkdir()
    proof = root / "proof.drat"
    proof.write_bytes(b"proof-prefix\n")
    prefix = resume_v1.stable_file_record(proof, relative_to=root)
    checkpoint = resume_v1.seal_manifest(
        "checkpoint.commit",
        {
            "generation": 0,
            "images": [],
            "proof_prefix": prefix,
            "single_writer_stopped": True,
        },
    )
    exact = resume_v1._validate_proof_before_resume(root, checkpoint, None)
    assert exact["injected_stale_tail"] is False

    marker = b"STALE-TAIL-FOR-TEST"
    with proof.open("ab") as handle:
        handle.write(marker)
    with pytest.raises(resume_v1.ResumeControllerError, match="uncommitted"):
        resume_v1._validate_proof_before_resume(root, checkpoint, None)

    injection = resume_v1.seal_manifest(
        "stale-tail.commit",
        {
            "checkpoint_manifest_sha256": checkpoint["self_sha256"],
            "generation": 0,
            "proof_after_injection": resume_v1.stable_file_record(
                proof, relative_to=root
            ),
            "stale_offset": prefix["bytes"],
            "stale_payload_hex": marker.hex(),
            "test_flag": resume_v1.STALE_FLAG,
        },
    )
    accepted = resume_v1._validate_proof_before_resume(
        root, checkpoint, injection
    )
    assert accepted["injected_stale_tail"] is True
    assert accepted["prefix_sha256"] == hashlib.sha256(b"proof-prefix\n").hexdigest()

    proof.write_bytes(b"X" + proof.read_bytes()[1:])
    with pytest.raises(resume_v1.ResumeControllerError, match="prefix hash"):
        resume_v1._validate_proof_before_resume(root, checkpoint, injection)


def test_stale_marker_must_disappear_after_restart(tmp_path: Path) -> None:
    proof = tmp_path / "proof.drat"
    marker = b"known-stale-marker"
    proof.write_bytes(b"prefix" + marker)
    preflight = {
        "injected_stale_tail": True,
        "stale_offset": 6,
        "stale_payload_hex": marker.hex(),
    }
    with pytest.raises(resume_v1.ResumeControllerError, match="failed to truncate"):
        resume_v1._assert_stale_marker_removed(proof, preflight)
    proof.write_bytes(b"prefixnew-search-data")
    resume_v1._assert_stale_marker_removed(proof, preflight)


def test_image_hash_and_uncompressed_magic_are_both_bound(tmp_path: Path) -> None:
    root = tmp_path / "root"
    image = root / "generations" / "000000" / "images" / "ckpt_x.dmtcp"
    image.parent.mkdir(parents=True)
    image.write_bytes(resume_v1.DMTCP_IMAGE_MAGIC + b"image")
    checkpoint = {
        "images": [resume_v1.stable_file_record(image, relative_to=root)]
    }
    assert resume_v1._verify_checkpoint_images(root, checkpoint) == [
        image.resolve()
    ]
    image.write_bytes(resume_v1.DMTCP_IMAGE_MAGIC + b"tampered")
    with pytest.raises(resume_v1.ResumeControllerError, match="binding mismatch"):
        resume_v1._verify_checkpoint_images(root, checkpoint)


def test_generation_gap_and_claim_without_commit_are_poison(tmp_path: Path) -> None:
    root = tmp_path / "root"
    (root / "generations" / "000001").mkdir(parents=True)
    with pytest.raises(resume_v1.ResumeControllerError, match="contiguous"):
        resume_v1._generation_numbers(root)

    gen = root / "generations" / "000001"
    resume_v1.write_manifest(
        gen / "resume.claim.json",
        "resume.claim",
        {"generation": 1},
    )
    assert resume_v1._claim_without_commit(gen) == "resume.claim.json"


def test_unsafe_dmtcp_environment_is_rejected() -> None:
    for name in resume_v1.UNSAFE_DMTCP_ENV:
        with pytest.raises(resume_v1.ResumeControllerError, match=name):
            resume_v1._check_unsafe_environment({name: "0"})


def test_stale_tail_cli_requires_visibly_explicit_test_flag(tmp_path: Path) -> None:
    with pytest.raises(resume_v1.ResumeControllerError, match="requires"):
        resume_v1.inject_stale_tail(tmp_path, explicit_test_flag=False)
    parsed = resume_v1.build_parser().parse_args(
        ["inject-stale-tail", "--root", str(tmp_path), resume_v1.STALE_FLAG]
    )
    assert parsed.test_only_allow_stale_tail is True


def test_dynamic_elf_requires_runtime_completeness_attestation(
    tmp_path: Path,
) -> None:
    prefix = _fake_dmtcp_prefix(tmp_path)
    cnf = tmp_path / "x.cnf"
    cnf.write_bytes(b"p cnf 0 0\n")
    with pytest.raises(
        resume_v1.ResumeControllerError, match="runtime-libs-complete"
    ):
        resume_v1.initialize(
            tmp_path / "root",
            cnf=cnf,
            solver=Path("/bin/true"),
            dmtcp_prefix=prefix,
            solver_args=[],
            runtime_libs=[],
            runtime_libs_complete=False,
        )


def test_source_is_stdlib_only_and_controller_is_test_only() -> None:
    source = SOURCE.read_text(encoding="utf-8")
    assert "import numpy" not in source
    assert "import pysat" not in source
    assert 'AUTHORITY = "TEST_ONLY"' in source
    assert "PRODUCTION" not in source
    assert "--ckpt-open-files" in source  # It is present only in the ban list/docs.
    assert "DMTCP_SKIP_TRUNCATE_FILE_AT_RESTART" in source
