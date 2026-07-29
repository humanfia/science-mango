from __future__ import annotations

import copy
import base64
import hashlib
import importlib.metadata
import os
import platform
import shutil
import stat
import sys
import time
from pathlib import Path

import pytest
from packaging.requirements import Requirement
from packaging.utils import canonicalize_name

from evaluation import proof_runtime as proof_runtime_module
from evaluation.proof_runtime import (
    PROOF_RUNTIME_ROOT_PACKAGES,
    PROOF_RUNTIME_PROBE_MAX_OUTPUT_BYTES,
    PROOF_RUNTIME_SCHEMA_VERSION,
    PROOF_RUNTIME_TRANSITIVE_PACKAGES,
    RuntimeProbeError,
    SOLVER_RUNTIME_PACKAGES,
    probe_python_runtime,
    proof_runtime_fingerprint,
    validate_proof_runtime_fingerprint,
)


NEW_PROOF_PACKAGES = {
    "sympy",
    "igraph",
    "python-igraph",
    "ldpc",
    "galois",
    "networkx",
}
PROOF_CRITICAL_TRANSITIVE_PACKAGES = {
    "absl-py",
    "clarabel",
    "cffi",
    "contourpy",
    "cvxpy",
    "cycler",
    "diskcache",
    "fonttools",
    "immutabledict",
    "jinja2",
    "joblib",
    "kiwisolver",
    "llvmlite",
    "markupsafe",
    "matplotlib",
    "mpmath",
    "numba",
    "osqp",
    "packaging",
    "pandas",
    "pillow",
    "platformdirs",
    "protobuf",
    "pycparser",
    "pymatching",
    "pyparsing",
    "python-dateutil",
    "pytz",
    "scs",
    "setuptools",
    "sinter",
    "six",
    "stim",
    "texttable",
    "tqdm",
    "typing-extensions",
}
PROOF_CRITICAL_DEPENDENCY_EDGES = {
    "ortools": {
        "absl-py",
        "immutabledict",
        "numpy",
        "pandas",
        "protobuf",
        "typing-extensions",
    },
    "qldpc": {
        "cvxpy",
        "diskcache",
        "galois",
        "ldpc",
        "networkx",
        "numpy",
        "platformdirs",
        "pymatching",
        "scipy",
        "stim",
        "sympy",
    },
    "galois": {"numba", "numpy", "typing-extensions"},
    "numba": {"llvmlite", "numpy"},
    "cvxpy": {"clarabel", "highspy", "numpy", "osqp", "scipy", "scs"},
    "pandas": {"numpy", "python-dateutil"},
    "python-igraph": {"igraph"},
    "igraph": {"texttable"},
    "sympy": {"mpmath"},
    "ldpc": {"numpy", "pymatching", "scipy", "sinter", "stim", "tqdm"},
    "pymatching": {"matplotlib", "networkx", "numpy", "scipy"},
    "sinter": {"matplotlib", "numpy", "scipy", "stim"},
    "matplotlib": {
        "contourpy",
        "cycler",
        "fonttools",
        "kiwisolver",
        "numpy",
        "packaging",
        "pillow",
        "pyparsing",
        "python-dateutil",
    },
    "osqp": {"jinja2", "joblib", "numpy", "scipy", "setuptools"},
    "jinja2": {"markupsafe"},
    "clarabel": {"cffi", "numpy", "scipy"},
    "cffi": {"pycparser"},
    "python-dateutil": {"six"},
}


@pytest.fixture(scope="module")
def local_runtime() -> dict[str, object]:
    return proof_runtime_fingerprint()


def _copy_current_python(destination: Path) -> Path:
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(Path(sys.executable).resolve(), destination)
    destination.chmod(destination.stat().st_mode | stat.S_IXUSR)
    venv_root = destination.parent.parent
    (venv_root / "pyvenv.cfg").write_text(
        "\n".join(
            [
                f"home = {Path(sys.base_prefix) / 'bin'}",
                "include-system-site-packages = false",
                f"version = {platform.python_version()}",
                f"executable = {Path(sys.executable).resolve()}",
                "",
            ]
        )
    )
    return destination


def _record_digest(value: bytes) -> str:
    return base64.urlsafe_b64encode(
        hashlib.sha256(value).digest(),
    ).rstrip(b"=").decode("ascii")


def _fake_single_file_distribution_venv(
    root: Path,
    *,
    distribution_name: str,
    import_path: str,
    version: str,
    package_source: str,
) -> tuple[Path, Path]:
    python = root / "bin" / "python"
    python.parent.mkdir(parents=True)
    python.symlink_to(Path(sys.executable).resolve())
    (root / "pyvenv.cfg").write_text(
        "\n".join(
            [
                f"home = {Path(sys.base_prefix) / 'bin'}",
                "include-system-site-packages = false",
                f"version = {platform.python_version()}",
                f"executable = {Path(sys.executable).resolve()}",
                "",
            ]
        )
    )
    site = root / "lib" / (
        f"python{sys.version_info.major}.{sys.version_info.minor}"
    ) / "site-packages"
    package = site / import_path
    package.parent.mkdir(parents=True)
    package.write_text(package_source)
    metadata_dir = site / (
        f"{distribution_name.replace('-', '_')}-{version}.dist-info"
    )
    metadata_dir.mkdir()
    metadata = metadata_dir / "METADATA"
    metadata.write_text(
        "Metadata-Version: 2.1\n"
        f"Name: {distribution_name}\n"
        f"Version: {version}\n"
    )
    record = metadata_dir / "RECORD"
    package_relative = package.relative_to(site).as_posix()
    metadata_relative = metadata.relative_to(site).as_posix()
    package_bytes = package.read_bytes()
    metadata_bytes = metadata.read_bytes()
    record.write_text(
        "\n".join(
            [
                (
                    f"{package_relative},sha256="
                    f"{_record_digest(package_bytes)},{len(package_bytes)}"
                ),
                (
                    f"{metadata_relative},sha256="
                    f"{_record_digest(metadata_bytes)},{len(metadata_bytes)}"
                ),
                f"{record.relative_to(site).as_posix()},,",
                "",
            ]
        )
    )
    return python, package


def _fake_networkx_venv(
    root: Path,
    *,
    package_source: str,
) -> tuple[Path, Path]:
    return _fake_single_file_distribution_venv(
        root,
        distribution_name="networkx",
        import_path="networkx/__init__.py",
        version="9.9.9",
        package_source=package_source,
    )


def _expect_probe_rejection(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    program: str,
    *,
    timeout: float = 10.0,
) -> RuntimeProbeError:
    monkeypatch.setattr(proof_runtime_module, "_PROBE_PROGRAM", program)
    with pytest.raises(RuntimeProbeError) as raised:
        probe_python_runtime(
            sys.executable,
            cwd=tmp_path,
            timeout=timeout,
        )
    return raised.value


def test_real_qcode_interpreter_local_fingerprint_matches_probe(
    local_runtime: dict[str, object],
    tmp_path: Path,
) -> None:
    probed = probe_python_runtime(
        sys.executable,
        cwd=tmp_path,
    )

    assert probed["runtime"] == local_runtime
    assert probed["interpreter"] == local_runtime["interpreter"]


def test_runtime_schema_one_is_rejected(
    local_runtime: dict[str, object],
) -> None:
    legacy = copy.deepcopy(local_runtime)
    legacy["schema_version"] = 1

    with pytest.raises(ValueError, match="schema is unsupported"):
        validate_proof_runtime_fingerprint(legacy)

    assert PROOF_RUNTIME_SCHEMA_VERSION != 1


@pytest.mark.parametrize("package", sorted(NEW_PROOF_PACKAGES))
def test_runtime_missing_new_proof_package_is_rejected(
    local_runtime: dict[str, object],
    package: str,
) -> None:
    incomplete = copy.deepcopy(local_runtime)
    incomplete["packages"].pop(package)

    with pytest.raises(ValueError, match="package identity is incomplete"):
        validate_proof_runtime_fingerprint(incomplete)


def test_runtime_missing_package_artifact_identity_is_rejected(
    local_runtime: dict[str, object],
) -> None:
    incomplete = copy.deepcopy(local_runtime)
    incomplete.pop("package_artifacts")

    with pytest.raises(ValueError, match="unexpected fields"):
        validate_proof_runtime_fingerprint(incomplete)


def test_solver_runtime_package_set_covers_all_proof_dependencies() -> None:
    assert NEW_PROOF_PACKAGES <= set(SOLVER_RUNTIME_PACKAGES)


def test_runtime_package_set_covers_fixed_proof_dependency_closure() -> None:
    bound = {canonicalize_name(name) for name in SOLVER_RUNTIME_PACKAGES}

    assert set(PROOF_RUNTIME_ROOT_PACKAGES) <= set(SOLVER_RUNTIME_PACKAGES)
    assert PROOF_CRITICAL_TRANSITIVE_PACKAGES == set(
        PROOF_RUNTIME_TRANSITIVE_PACKAGES,
    )
    assert PROOF_CRITICAL_TRANSITIVE_PACKAGES <= bound
    for parent, expected_dependencies in (
        PROOF_CRITICAL_DEPENDENCY_EDGES.items()
    ):
        declared = {
            canonicalize_name(Requirement(requirement).name)
            for requirement in (
                importlib.metadata.requires(parent) or ()
            )
        }
        expected = {
            canonicalize_name(name) for name in expected_dependencies
        }
        assert expected <= declared, parent
        assert expected <= bound, parent


def test_configured_worker_runtime_is_distinct_from_controller_runtime(
    local_runtime: dict[str, object],
    tmp_path: Path,
) -> None:
    worker_python = _copy_current_python(
        tmp_path / "worker" / "bin" / "python",
    )
    worker = probe_python_runtime(
        str(worker_python),
        cwd=tmp_path,
    )["runtime"]

    assert worker != local_runtime
    assert worker["interpreter"]["realpath"] == str(worker_python)
    assert (
        worker["interpreter"]["executable_file"]
        != local_runtime["interpreter"]["executable_file"]
    )


@pytest.mark.parametrize("stream", ["stdout", "stderr"])
def test_probe_rejects_any_unexpected_diagnostic_output(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    stream: str,
) -> None:
    descriptor = 1 if stream == "stdout" else 2
    program = (
        proof_runtime_module._PROBE_PROGRAM
        + f"\nos.write({descriptor}, b'unexpected-{stream}')"
    )

    error = _expect_probe_rejection(monkeypatch, tmp_path, program)

    assert "unexpected stdout or stderr" in str(error)


def test_probe_rejects_noncanonical_json(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    canonical_program = proof_runtime_module._PROBE_PROGRAM
    assert "sort_keys=True," in canonical_program
    noncanonical_program = canonical_program.replace(
        "sort_keys=True,",
        "sort_keys=False,",
        1,
    )

    error = _expect_probe_rejection(
        monkeypatch,
        tmp_path,
        noncanonical_program,
    )

    assert "not canonical JSON" in str(error)


def test_probe_rejects_duplicate_json_keys(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    duplicate_key_program = r"""
import os
import struct
import sys

descriptor = int(sys.argv[1])
encoded = b'{"duplicate":1,"duplicate":2}'
frame = struct.pack(">I", len(encoded)) + encoded
offset = 0
while offset < len(frame):
    offset += os.write(descriptor, frame[offset:])
os.close(descriptor)
""".strip()

    error = _expect_probe_rejection(
        monkeypatch,
        tmp_path,
        duplicate_key_program,
    )

    assert "duplicate key" in str(error)


def test_probe_timeout_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    error = _expect_probe_rejection(
        monkeypatch,
        tmp_path,
        "import time\ntime.sleep(60)",
        timeout=0.05,
    )

    assert "timed out" in str(error)


def test_probe_timeout_kills_child_after_leader_exits(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    child_identity = tmp_path / "probe-child.txt"
    program = f"""
import os
import time
from pathlib import Path

child = os.fork()
if child:
    os._exit(0)
Path({str(child_identity)!r}).write_text(
    f"{{os.getpid()}} {{os.getpgrp()}} {{os.getsid(0)}}"
)
time.sleep(60)
""".strip()

    error = _expect_probe_rejection(
        monkeypatch,
        tmp_path,
        program,
        timeout=0.25,
    )

    assert "timed out" in str(error)
    child_pid, child_pgid, child_session = map(
        int,
        child_identity.read_text().split(),
    )
    assert child_pid != child_pgid
    assert child_pgid == child_session
    deadline = time.monotonic() + 2
    while time.monotonic() < deadline:
        stat_path = Path("/proc") / str(child_pid) / "stat"
        try:
            fields = stat_path.read_text().rsplit(")", 1)[1].split()
        except (FileNotFoundError, IndexError):
            break
        if fields[0] == "Z":
            break
        time.sleep(0.01)
    else:
        pytest.fail(f"probe descendant survived cleanup: pid={child_pid}")


def test_probe_cleanup_refuses_current_process_group() -> None:
    _state, identity = proof_runtime_module._read_probe_process_identity(
        os.getpid(),
    )

    with pytest.raises(RuntimeProbeError, match="current proof controller"):
        proof_runtime_module._validate_isolated_probe_identity(
            identity,
            expected_pid=os.getpid(),
        )


def test_probe_protocol_output_over_limit_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    over_limit_program = f"""
import os
import sys

descriptor = int(sys.argv[1])
payload = b"x" * ({PROOF_RUNTIME_PROBE_MAX_OUTPUT_BYTES} + 16)
offset = 0
while offset < len(payload):
    offset += os.write(descriptor, payload[offset:])
os.close(descriptor)
""".strip()

    error = _expect_probe_rejection(
        monkeypatch,
        tmp_path,
        over_limit_program,
    )

    assert "protocol exceeded the limit" in str(error)


def test_symlink_retarget_changes_interpreter_identity(
    tmp_path: Path,
) -> None:
    first_python = _copy_current_python(
        tmp_path / "first" / "bin" / "python",
    )
    second_python = _copy_current_python(
        tmp_path / "second" / "bin" / "python",
    )
    invocation_root = tmp_path / "invocation"
    invocation = invocation_root / "bin" / "python-worker"
    invocation.parent.mkdir(parents=True)
    (invocation_root / "pyvenv.cfg").write_text(
        (first_python.parent.parent / "pyvenv.cfg").read_text()
    )
    invocation.symlink_to(first_python)
    first = probe_python_runtime(
        str(invocation),
        cwd=tmp_path,
    )["runtime"]

    invocation.unlink()
    invocation.symlink_to(second_python)
    second = probe_python_runtime(
        str(invocation),
        cwd=tmp_path,
    )["runtime"]

    assert first != second
    assert first["interpreter"]["realpath"] == str(first_python)
    assert second["interpreter"]["realpath"] == str(second_python)
    assert (
        first["interpreter"]["invocation_lstat"]
        != second["interpreter"]["invocation_lstat"]
    )


def test_executable_content_change_changes_file_identity(
    tmp_path: Path,
) -> None:
    worker_python = _copy_current_python(
        tmp_path / "worker" / "bin" / "python",
    )
    before = probe_python_runtime(
        str(worker_python),
        cwd=tmp_path,
    )["runtime"]

    with worker_python.open("ab") as stream:
        stream.write(b"qcode-runtime-identity-regression-test")

    after = probe_python_runtime(
        str(worker_python),
        cwd=tmp_path,
    )["runtime"]

    before_file = before["interpreter"]["executable_file"]
    after_file = after["interpreter"]["executable_file"]
    assert before != after
    assert before_file["sha256"] != after_file["sha256"]
    assert before_file["bytes"] < after_file["bytes"]


def test_same_version_different_distribution_contents_change_identity(
    tmp_path: Path,
) -> None:
    first_python, _ = _fake_networkx_venv(
        tmp_path / "first",
        package_source="BUILD = 'first'\n",
    )
    second_python, _ = _fake_networkx_venv(
        tmp_path / "second",
        package_source="BUILD = 'second'\n",
    )

    first = probe_python_runtime(
        str(first_python),
        cwd=tmp_path,
    )["runtime"]["package_artifacts"]["networkx"]
    second = probe_python_runtime(
        str(second_python),
        cwd=tmp_path,
    )["runtime"]["package_artifacts"]["networkx"]

    assert first["version"] == second["version"] == "9.9.9"
    assert first["files_sha256"] != second["files_sha256"]
    assert first["import_origin"]["file_identity"]["sha256"] != (
        second["import_origin"]["file_identity"]["sha256"]
    )


def test_same_version_transitive_dependency_contents_change_identity(
    tmp_path: Path,
) -> None:
    first_python, _ = _fake_single_file_distribution_venv(
        tmp_path / "transitive-first",
        distribution_name="typing-extensions",
        import_path="typing_extensions.py",
        version="9.9.9",
        package_source="BUILD = 'first'\n",
    )
    second_python, _ = _fake_single_file_distribution_venv(
        tmp_path / "transitive-second",
        distribution_name="typing-extensions",
        import_path="typing_extensions.py",
        version="9.9.9",
        package_source="BUILD = 'second'\n",
    )

    first = probe_python_runtime(
        str(first_python),
        cwd=tmp_path,
    )["runtime"]["package_artifacts"]["typing-extensions"]
    second = probe_python_runtime(
        str(second_python),
        cwd=tmp_path,
    )["runtime"]["package_artifacts"]["typing-extensions"]

    assert first["version"] == second["version"] == "9.9.9"
    assert first["files_sha256"] != second["files_sha256"]
    assert first["import_origin"]["file_identity"]["sha256"] != (
        second["import_origin"]["file_identity"]["sha256"]
    )


def test_same_version_local_patch_with_stale_record_fails_closed(
    tmp_path: Path,
) -> None:
    python, package = _fake_networkx_venv(
        tmp_path / "patched",
        package_source="BUILD = 'pinned'\n",
    )
    probe_python_runtime(str(python), cwd=tmp_path)
    package.write_text("BUILD = 'locally-patched-without-record-update'\n")

    with pytest.raises(RuntimeProbeError):
        probe_python_runtime(str(python), cwd=tmp_path)


@pytest.mark.parametrize("mutation", ["missing", "symlink"])
def test_record_file_missing_or_symlink_fails_closed(
    tmp_path: Path,
    mutation: str,
) -> None:
    python, package = _fake_networkx_venv(
        tmp_path / mutation,
        package_source="BUILD = 'regular'\n",
    )
    package.unlink()
    if mutation == "symlink":
        replacement = package.with_name("replacement.py")
        replacement.write_text("BUILD = 'replacement'\n")
        package.symlink_to(replacement)

    with pytest.raises(RuntimeProbeError):
        probe_python_runtime(str(python), cwd=tmp_path)


def test_probe_records_project_shadow_import_origin(
    tmp_path: Path,
) -> None:
    shadow = tmp_path / "networkx.py"
    shadow.write_text("SHADOW = True\n")

    runtime = probe_python_runtime(
        sys.executable,
        cwd=tmp_path,
    )["runtime"]
    origin = runtime["package_artifacts"]["networkx"]["import_origin"]

    assert origin["origin"] == str(shadow)
    assert origin["file_identity"]["sha256"] == hashlib.sha256(
        shadow.read_bytes()
    ).hexdigest()
