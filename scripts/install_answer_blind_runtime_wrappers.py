#!/usr/bin/env python3
"""Install root-owned launchers for answer-blind runtime components.

Run this trusted-controller utility as root after installing the audited
Archon wheel into the dedicated runtime venv.  It never reads a solver
workspace and makes the MCP server import only from the root-owned wheel.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import shutil
import stat
import subprocess
import tempfile
from pathlib import Path


SOURCE_ROOT = Path(__file__).resolve().parent
PYTHON_CACHE_DIRS = {
    "__pycache__",
    ".pytest_cache",
    ".mypy_cache",
    ".ruff_cache",
}
CODEX_VERSION_RE = re.compile(
    r"^codex-cli (?P<version>[0-9]+(?:\.[0-9]+){2}(?:[-+][A-Za-z0-9._-]+)?)$",
    re.MULTILINE,
)

# ``check_axioms_inline.sh`` runs inside the solver's restricted PATH.  This is
# the complete external-command surface found by auditing that script; ``echo``
# and ``pwd`` are Bash builtins, while ``lake`` comes from the sealed Lean
# toolchain's bin directory.  Keep these as individual immutable files -- never
# grant the solver either system bin directory itself.
AXIOM_CHECKER_SYSTEM_TOOLS = (
    "mktemp",
    "awk",
    "cat",
    "mv",
    "rm",
    "find",
    "realpath",
    "dirname",
    "basename",
    "sort",
    "cp",
    "grep",
    "head",
    "cut",
    "sed",
)
TRUSTED_SYSTEM_BIN_DIRS = (Path("/usr/bin"), Path("/bin"))


def _inside(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def _make_root_readonly(root: Path) -> None:
    for directory, names, files in os.walk(root, topdown=False, followlinks=False):
        base = Path(directory)
        for name in sorted(files):
            path = base / name
            if path.is_symlink():
                os.lchown(path, 0, 0)
                continue
            os.chown(path, 0, 0)
            os.chmod(path, stat.S_IMODE(path.stat().st_mode) & ~0o022)
        for name in sorted(names):
            path = base / name
            if path.is_symlink():
                os.lchown(path, 0, 0)
                continue
            os.chown(path, 0, 0)
            os.chmod(path, stat.S_IMODE(path.stat().st_mode) & ~0o022)
    os.chown(root, 0, 0)
    os.chmod(root, stat.S_IMODE(root.stat().st_mode) & ~0o022)


def _purge_python_caches(root: Path) -> None:
    """Remove non-source interpreter caches before sealing the runtime."""

    for path in sorted(root.rglob("*"), key=lambda item: len(item.parts), reverse=True):
        if path.is_symlink():
            continue
        if path.is_file() and path.suffix in {".pyc", ".pyo"}:
            path.unlink()
        elif path.is_dir() and path.name in PYTHON_CACHE_DIRS:
            shutil.rmtree(path)


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _validate_trusted_executable(path: Path) -> Path:
    """Return one resolved, immutable root-owned executable or fail closed."""

    resolved = path.resolve(strict=True)
    metadata = resolved.stat(follow_symlinks=False)
    mode = stat.S_IMODE(metadata.st_mode)
    if not stat.S_ISREG(metadata.st_mode):
        raise PermissionError(f"controller tool is not a regular file: {resolved}")
    if metadata.st_uid != 0:
        raise PermissionError(f"controller tool is not root-owned: {resolved}")
    if mode & 0o022:
        raise PermissionError(
            f"controller tool is group/world-writable: {resolved}"
        )
    if mode & 0o111 == 0:
        raise PermissionError(f"controller tool is not executable: {resolved}")
    return resolved


def _resolve_trusted_system_executable(name: str) -> Path:
    """Resolve a named host tool only from fixed, root-owned system dirs."""

    if re.fullmatch(r"[a-z][a-z0-9-]*", name) is None:
        raise ValueError(f"invalid system tool name: {name!r}")

    trusted_roots: list[Path] = []
    for raw_root in TRUSTED_SYSTEM_BIN_DIRS:
        try:
            root = raw_root.resolve(strict=True)
            metadata = root.stat(follow_symlinks=False)
        except FileNotFoundError:
            continue
        if (
            not stat.S_ISDIR(metadata.st_mode)
            or metadata.st_uid != 0
            or stat.S_IMODE(metadata.st_mode) & 0o022
        ):
            raise PermissionError(f"untrusted system tool directory: {raw_root}")
        if root not in trusted_roots:
            trusted_roots.append(root)

    for raw_root in TRUSTED_SYSTEM_BIN_DIRS:
        candidate = raw_root / name
        try:
            resolved = candidate.resolve(strict=True)
        except FileNotFoundError:
            continue
        if not any(_inside(resolved, root) for root in trusted_roots):
            raise PermissionError(
                f"system tool resolves outside trusted bin directories: {candidate}"
            )
        return _validate_trusted_executable(resolved)
    raise FileNotFoundError(f"required axiom-checker tool is unavailable: {name}")


def _codex_version(binary: Path) -> str:
    completed = subprocess.run(
        [str(binary), "--version"],
        check=False,
        capture_output=True,
        text=True,
        timeout=10,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"standalone Codex version probe failed with {completed.returncode}"
        )
    output = f"{completed.stdout}\n{completed.stderr}"
    matches = [match.group("version") for match in CODEX_VERSION_RE.finditer(output)]
    if len(matches) != 1:
        raise RuntimeError("standalone Codex emitted no unique codex-cli version")
    return matches[0]


def _resolve_standalone_codex_pair() -> tuple[Path, Path, str]:
    """Resolve Codex and its host from one versioned standalone release.

    The host is deliberately not resolved independently from ``PATH``.  Doing
    that could silently pair a new CLI with a stale protocol implementation.
    A valid install is the exact sibling pair shipped under a versioned
    ``standalone/releases/<version>-<target>/bin`` directory.
    """

    raw_codex = shutil.which("codex")
    if not raw_codex:
        raise FileNotFoundError("required controller tool is unavailable: codex")
    codex = Path(raw_codex).resolve(strict=True)
    release_bin = codex.parent
    release = release_bin.parent
    if (
        codex.name != "codex"
        or release_bin.name != "bin"
        or release.parent.name != "releases"
        or release.parent.parent.name != "standalone"
    ):
        raise RuntimeError(
            "codex must resolve inside a versioned standalone release"
        )

    host_candidate = release_bin / "codex-code-mode-host"
    try:
        host = host_candidate.resolve(strict=True)
    except FileNotFoundError as exc:
        raise FileNotFoundError(
            f"standalone Codex release is missing sibling host: {host_candidate}"
        ) from exc
    if host.parent != release_bin or host.name != "codex-code-mode-host":
        raise RuntimeError("Codex host must be an in-release sibling of codex")
    if not codex.is_file() or not host.is_file():
        raise FileNotFoundError("standalone Codex pair must contain regular files")

    version = _codex_version(codex)
    if not release.name.startswith(f"{version}-"):
        raise RuntimeError(
            f"Codex binary version {version} does not match release {release.name}"
        )
    return codex, host, version


def _copy_verified_executable(
    source: Path,
    destination: Path,
    *,
    require_root_owned_source: bool = False,
) -> str:
    """Atomically install one exact, immutable root-owned executable."""

    source = source.resolve(strict=True)
    if require_root_owned_source:
        source = _validate_trusted_executable(source)
    before = _sha256(source)
    temporary = destination.with_name(f".{destination.name}.answer-blind.tmp")
    if temporary.exists() or temporary.is_symlink():
        raise FileExistsError(f"unsafe stale runtime executable: {temporary}")
    try:
        shutil.copyfile(source, temporary)
        copied = _sha256(temporary)
        after = _sha256(source)
        if before != copied or before != after:
            raise RuntimeError(f"controller tool changed while copying: {source}")
        if require_root_owned_source:
            _validate_trusted_executable(source)
        os.chown(temporary, 0, 0)
        os.chmod(temporary, 0o555)
        os.replace(temporary, destination)
    finally:
        if temporary.exists() or temporary.is_symlink():
            temporary.unlink()

    installed = destination.stat(follow_symlinks=False)
    if (
        not stat.S_ISREG(installed.st_mode)
        or installed.st_uid != 0
        or stat.S_IMODE(installed.st_mode) != 0o555
    ):
        raise PermissionError(
            f"installed controller tool ownership/mode is invalid: {destination}"
        )
    if _sha256(destination) != before:
        raise RuntimeError(f"installed controller tool hash mismatch: {destination}")
    return before


def _materialize_python(root: Path) -> Path:
    """Keep the venv's base interpreter inside the trusted runtime.

    A venv symlink into a developer-owned ``/usr/local`` tree lets that owner
    replace Python or its standard library after the runtime was inventoried.
    Copy the complete base installation and rewrite internal absolute links so
    both the executable and ``sys.base_prefix`` remain under ``runtime_root``.
    """

    venv = root / "venv"
    python_link = venv / "bin/python"
    source_python = python_link.resolve(strict=True)
    if _inside(source_python, root):
        return source_python
    source_root = source_python.parent.parent.resolve(strict=True)
    destination = root / "python"
    if destination.exists() or destination.is_symlink():
        raise FileExistsError(
            "runtime Python destination already exists but venv still points outside"
        )
    staging = Path(tempfile.mkdtemp(prefix=".answer-blind-python-", dir=root))
    candidate = staging / "python"
    try:
        shutil.copytree(source_root, candidate, symlinks=True)
        for directory, names, files in os.walk(candidate, followlinks=False):
            base = Path(directory)
            for name in [*names, *files]:
                link = base / name
                if not link.is_symlink():
                    continue
                raw_target = Path(os.readlink(link))
                if not raw_target.is_absolute():
                    continue
                try:
                    relative_target = raw_target.relative_to(source_root)
                except ValueError as exc:
                    raise RuntimeError(
                        f"base Python contains external absolute symlink: {link}"
                    ) from exc
                new_target = candidate / relative_target
                link.unlink()
                link.symlink_to(os.path.relpath(new_target, start=link.parent))
        _make_root_readonly(candidate)
        os.replace(candidate, destination)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    else:
        shutil.rmtree(staging, ignore_errors=True)

    relative_binary = source_python.relative_to(source_root)
    trusted_python = destination / relative_binary
    temporary_link = python_link.with_name(".python.answer-blind.tmp")
    temporary_link.symlink_to(trusted_python)
    os.replace(temporary_link, python_link)
    for name in ("python3", f"python{source_python.name.removeprefix('python')}"):
        link = venv / "bin" / name
        if link == python_link:
            continue
        if link.exists() or link.is_symlink():
            link.unlink()
        link.symlink_to("python")
        os.lchown(link, 0, 0)

    config = venv / "pyvenv.cfg"
    lines = config.read_text(encoding="utf-8").splitlines()
    rewritten = [
        f"home = {trusted_python.parent}" if line.startswith("home = ") else line
        for line in lines
    ]
    config.write_text("\n".join(rewritten) + "\n", encoding="utf-8")
    os.chown(config, 0, 0)
    os.chmod(config, 0o644)
    return trusted_python


def _copy_controller_tools(root: Path) -> None:
    """Copy the small tool surface agents need into the sealed runtime.

    Landlock never grants `/usr` or `/bin` directory access.  Copies are
    inventory-bound with the rest of the runtime; ELF library dependencies
    remain exact-file grants recorded by the launch authorization.
    """

    # Resolve every source, including the complete Codex release pair, before
    # mutating the runtime.  In particular, a missing host must fail closed
    # without leaving a deceptively usable standalone ``codex`` behind.
    sources: dict[str, Path] = {}
    for name in ("bash", "dash", "git", "rg", "ssh"):
        source = shutil.which(name)
        if not source:
            raise FileNotFoundError(f"required controller tool is unavailable: {name}")
        sources[name] = Path(source).resolve(strict=True)
    for name in AXIOM_CHECKER_SYSTEM_TOOLS:
        sources[name] = _resolve_trusted_system_executable(name)
    codex, codex_host, _codex_release_version = _resolve_standalone_codex_pair()
    sources["codex"] = codex
    sources["codex-code-mode-host"] = codex_host

    bin_dir = root / "bin"
    bin_dir.mkdir(mode=0o755, parents=True, exist_ok=True)
    for name, source in sources.items():
        _copy_verified_executable(
            source,
            bin_dir / name,
            require_root_owned_source=name in AXIOM_CHECKER_SYSTEM_TOOLS,
        )
    sh_link = bin_dir / "sh"
    temporary = bin_dir / ".sh.answer-blind.tmp"
    if temporary.exists() or temporary.is_symlink():
        raise FileExistsError(f"unsafe stale runtime link: {temporary}")
    temporary.symlink_to("dash")
    os.replace(temporary, sh_link)
    os.lchown(sh_link, 0, 0)


def install(*, runtime_root: Path, materialize_python: bool = True) -> Path:
    root = runtime_root.resolve()
    if os.geteuid() != 0:
        raise PermissionError("runtime wrappers must be installed by root")
    if materialize_python:
        _materialize_python(root)
    _copy_controller_tools(root)
    python = root / "venv/bin/python"
    candidates = list(
        (root / "venv/lib").glob(
            "python*/site-packages/archon/.archon-src/tools/lean-lsp-mcp/src"
        )
    )
    if len(candidates) != 1:
        raise FileNotFoundError("runtime must contain exactly one Archon MCP package")
    module_root = candidates[0]
    if not python.exists() or not module_root.joinpath("lean_lsp_mcp/__main__.py").is_file():
        raise FileNotFoundError("audited runtime wheel does not contain lean-lsp-mcp")
    bin_dir = root / "bin"
    bin_dir.mkdir(parents=True, exist_ok=True)
    wrapper = bin_dir / "lean-lsp-mcp-trusted"
    jail_source = SOURCE_ROOT / "answer_blind_mcp_jail.py"
    jail = root / "libexec/answer-blind-mcp-jail.py"
    jail.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
    shutil.copy2(jail_source, jail)
    os.chown(jail, 0, 0)
    os.chmod(jail, 0o555)
    payload = (
        f"#!{bin_dir / 'sh'}\n"
        "set -eu\n"
        "unset PYTHONHOME ANTHROPIC_API_KEY ANTHROPIC_AUTH_TOKEN "
        "ANTHROPIC_BASE_URL OPENAI_API_KEY OPENAI_ORG_ID OPENAI_PROJECT_ID "
        "HF_TOKEN HUGGING_FACE_HUB_TOKEN LEANEXPLORE_API_KEY\n"
        "export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1\n"
        "unset PYTHONPATH\n"
        f"exec '{python}' -P '{jail}'\n"
    ).encode("utf-8")
    temporary = wrapper.with_name(".lean-lsp-mcp-trusted.tmp")
    temporary.write_bytes(payload)
    temporary.chmod(0o755)
    os.replace(temporary, wrapper)
    if wrapper.stat().st_uid != 0 or stat.S_IMODE(wrapper.stat().st_mode) != 0o755:
        raise PermissionError("trusted MCP wrapper ownership/mode is invalid")
    archon = bin_dir / "archon"
    archon_payload = (
        f"#!{bin_dir / 'sh'}\n"
        "set -eu\n"
        "unset PYTHONHOME PYTHONPATH\n"
        "export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1\n"
        f"exec '{python}' -P -m archon.cli \"$@\"\n"
    ).encode("utf-8")
    archon_temporary = archon.with_name(".archon.tmp")
    archon_temporary.write_bytes(archon_payload)
    archon_temporary.chmod(0o755)
    os.replace(archon_temporary, archon)
    os.chown(archon, 0, 0)

    # The credential-holding broker must execute from the same sealed runtime,
    # never from a developer checkout or a solver workspace.  Keep the audited
    # Python source as an inventory-bound libexec file and expose a tiny wrapper
    # whose interpreter is the materialized runtime Python.
    broker_source = Path(__file__).with_name("run_answer_blind_model_broker.py")
    if broker_source.is_symlink() or not broker_source.is_file():
        raise FileNotFoundError("answer-blind model broker source is unavailable")
    libexec = root / "libexec"
    libexec.mkdir(mode=0o755, exist_ok=True)
    broker_module = libexec / "run_answer_blind_model_broker.py"
    shutil.copy2(broker_source, broker_module)
    os.chown(broker_module, 0, 0)
    os.chmod(broker_module, 0o444)
    structured_sources = (
        "run_answer_blind_structured_solver.py",
        "run_answer_blind_chatgpt_login_proxy.py",
        "run_answer_blind_gpt_campaign.py",
        "run_answer_blind_archon_campaign.py",
        "run_answer_blind_archon_isolated_campaign.py",
        "run_answer_blind_iteration.py",
        "build_answer_blind_solver_seed.py",
        "configure_answer_blind_workspace.py",
    )
    for source_name in structured_sources:
        source = Path(__file__).with_name(source_name)
        destination = libexec / source_name
        shutil.copy2(source, destination)
        os.chown(destination, 0, 0)
        os.chmod(destination, 0o444)
    reviewer_source = Path(__file__).with_name("run_answer_blind_independent_review.py")
    reviewer_module = libexec / "run_answer_blind_independent_review.py"
    shutil.copy2(reviewer_source, reviewer_module)
    os.chown(reviewer_module, 0, 0)
    os.chmod(reviewer_module, 0o444)
    verifier_source = Path(__file__).with_name("run_answer_blind_verifier.py")
    verifier_module = libexec / "run_answer_blind_verifier.py"
    shutil.copy2(verifier_source, verifier_module)
    os.chown(verifier_module, 0, 0)
    os.chmod(verifier_module, 0o444)
    broker = bin_dir / "answer-blind-model-broker"
    broker_payload = (
        f"#!{bin_dir / 'sh'}\n"
        "set -eu\n"
        "unset PYTHONHOME PYTHONPATH ANTHROPIC_API_KEY ANTHROPIC_AUTH_TOKEN "
        "ANTHROPIC_BASE_URL OPENAI_API_KEY OPENAI_ORG_ID OPENAI_PROJECT_ID "
        "HF_TOKEN HUGGING_FACE_HUB_TOKEN LEANEXPLORE_API_KEY\n"
        "export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1\n"
        f"exec '{python}' -P '{broker_module}' \"$@\"\n"
    ).encode("utf-8")
    broker_temporary = broker.with_name(".answer-blind-model-broker.tmp")
    broker_temporary.write_bytes(broker_payload)
    broker_temporary.chmod(0o755)
    os.replace(broker_temporary, broker)
    os.chown(broker, 0, 0)
    structured = bin_dir / "answer-blind-structured-solver"
    structured_payload = (
        f"#!{bin_dir / 'sh'}\n"
        "set -eu\n"
        "unset PYTHONHOME PYTHONPATH OPENAI_API_KEY ANTHROPIC_API_KEY "
        "ANTHROPIC_AUTH_TOKEN HF_TOKEN HUGGING_FACE_HUB_TOKEN\n"
        "export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1\n"
        f"exec '{python}' -P '{libexec / 'run_answer_blind_structured_solver.py'}' \"$@\"\n"
    ).encode("utf-8")
    structured_temporary = structured.with_name(".answer-blind-structured-solver.tmp")
    structured_temporary.write_bytes(structured_payload)
    structured_temporary.chmod(0o755)
    os.replace(structured_temporary, structured)
    os.chown(structured, 0, 0)
    reviewer = bin_dir / "answer-blind-independent-review"
    reviewer_payload = (
        f"#!{bin_dir / 'sh'}\n"
        "set -eu\n"
        "unset PYTHONHOME PYTHONPATH OPENAI_API_KEY OPENAI_ORG_ID "
        "OPENAI_PROJECT_ID ANTHROPIC_API_KEY ANTHROPIC_AUTH_TOKEN "
        "ANTHROPIC_BASE_URL HF_TOKEN HUGGING_FACE_HUB_TOKEN "
        "LEANEXPLORE_API_KEY\n"
        "export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1\n"
        f"exec '{python}' -P '{reviewer_module}' \"$@\"\n"
    ).encode("utf-8")
    reviewer_temporary = reviewer.with_name(".answer-blind-independent-review.tmp")
    reviewer_temporary.write_bytes(reviewer_payload)
    reviewer_temporary.chmod(0o755)
    os.replace(reviewer_temporary, reviewer)
    os.chown(reviewer, 0, 0)
    verifier = bin_dir / "answer-blind-verifier"
    verifier_payload = (
        f"#!{bin_dir / 'sh'}\n"
        "set -eu\n"
        "unset PYTHONHOME PYTHONPATH OPENAI_API_KEY OPENAI_ORG_ID "
        "OPENAI_PROJECT_ID ANTHROPIC_API_KEY ANTHROPIC_AUTH_TOKEN "
        "ANTHROPIC_BASE_URL HF_TOKEN HUGGING_FACE_HUB_TOKEN "
        "LEANEXPLORE_API_KEY\n"
        "export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1\n"
        f"exec '{python}' -P '{verifier_module}' \"$@\"\n"
    ).encode("utf-8")
    verifier_temporary = verifier.with_name(".answer-blind-verifier.tmp")
    verifier_temporary.write_bytes(verifier_payload)
    verifier_temporary.chmod(0o755)
    os.replace(verifier_temporary, verifier)
    os.chown(verifier, 0, 0)
    campaign_module = libexec / "run_answer_blind_gpt_campaign.py"
    campaign = bin_dir / "answer-blind-gpt-campaign"
    campaign_payload = (
        f"#!{bin_dir / 'sh'}\n"
        "set -eu\n"
        "unset PYTHONHOME PYTHONPATH OPENAI_API_KEY OPENAI_ORG_ID "
        "OPENAI_PROJECT_ID ANTHROPIC_API_KEY ANTHROPIC_AUTH_TOKEN "
        "ANTHROPIC_BASE_URL HF_TOKEN HUGGING_FACE_HUB_TOKEN "
        "LEANEXPLORE_API_KEY\n"
        "export PYTHONSAFEPATH=1 PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1\n"
        f"exec '{python}' -I -B '{campaign_module}' \"$@\"\n"
    ).encode("utf-8")
    campaign_temporary = campaign.with_name(".answer-blind-gpt-campaign.tmp")
    campaign_temporary.write_bytes(campaign_payload)
    campaign_temporary.chmod(0o755)
    os.replace(campaign_temporary, campaign)
    os.chown(campaign, 0, 0)
    isolated_module = libexec / "run_answer_blind_archon_isolated_campaign.py"
    isolated = bin_dir / "answer-blind-archon-isolated-campaign"
    isolated_payload = (
        f"#!{bin_dir / 'sh'}\n"
        "set -eu\n"
        "unset PYTHONHOME PYTHONPATH OPENAI_API_KEY OPENAI_ORG_ID "
        "OPENAI_PROJECT_ID ANTHROPIC_API_KEY ANTHROPIC_AUTH_TOKEN "
        "ANTHROPIC_BASE_URL HF_TOKEN HUGGING_FACE_HUB_TOKEN "
        "LEANEXPLORE_API_KEY\n"
        "export PYTHONSAFEPATH=1 PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1\n"
        f"exec '{python}' -I -B '{isolated_module}' \"$@\"\n"
    ).encode("utf-8")
    isolated_temporary = isolated.with_name(
        ".answer-blind-archon-isolated-campaign.tmp"
    )
    isolated_temporary.write_bytes(isolated_payload)
    isolated_temporary.chmod(0o755)
    os.replace(isolated_temporary, isolated)
    os.chown(isolated, 0, 0)
    _purge_python_caches(root)
    if any(
        path.name in PYTHON_CACHE_DIRS or path.suffix in {".pyc", ".pyo"}
        for path in root.rglob("*")
    ):
        raise RuntimeError("answer-blind runtime still contains Python cache artifacts")
    _make_root_readonly(libexec)
    return wrapper


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime-root", type=Path, required=True)
    parser.add_argument(
        "--no-materialize-python",
        action="store_true",
        help="Only for an already self-contained runtime.",
    )
    args = parser.parse_args()
    print(
        install(
            runtime_root=args.runtime_root,
            materialize_python=not args.no_materialize_python,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
