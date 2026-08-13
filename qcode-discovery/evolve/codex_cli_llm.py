"""OpenEvolve LLM adapter backed by an authenticated Codex CLI.

This is intentionally a text-generation boundary. Every invocation is a fresh,
ephemeral, read-only Codex session; OpenEvolve owns all evolutionary memory.
"""

from __future__ import annotations

import asyncio
import os
import re
import shutil
import stat
import subprocess
import tempfile
from pathlib import Path
from typing import Any


PROJECT_ROOT = Path(__file__).resolve().parent.parent
_ISOLATED_VIEW_ENV = "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST"
_ISOLATED_VIEW_SHA_ENV = "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST_SHA256"
_ISOLATED_SOURCE_SHA_ENV = (
    "QCODE_ANSATZ_V3_CODEX_VIEW_SOURCE_FINGERPRINT_SHA256"
)
_ISOLATED_BOUNDARY_ENV = "QCODE_ANSATZ_V3_CODEX_FILESYSTEM_BOUNDARY"
_CHROOT_USER = 65534
_CHROOT_CODEX_PATH = "/bin/codex"
_CHROOT_CODEX_ENVIRONMENT = {
    "HOME": "/root",
    "CODEX_HOME": "/root/.codex",
    "PATH": "/bin:/usr/bin",
    "SSL_CERT_FILE": "/etc/ssl/certs/ca-certificates.crt",
}
_CHROOT_CODEX_CONFIG_OVERRIDES = (
    "features.shell_tool=false",
    "features.unified_exec=false",
    "features.apps=false",
    "features.code_mode.enabled=false",
    "tools.view_image=false",
    'web_search="disabled"',
)


def _copy_regular(source: Path, destination: Path, *, mode: int = 0o555) -> None:
    source = source.resolve(strict=True)
    if not source.is_file():
        raise RuntimeError(f"Codex chroot source is not regular: {source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
    destination.chmod(mode)


def _dynamic_dependencies(path: Path) -> tuple[Path, ...]:
    try:
        completed = subprocess.run(
            ["ldd", str(path)],
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return ()
    if completed.returncode != 0:
        return ()
    dependencies: set[Path] = set()
    for line in completed.stdout.splitlines():
        matched = re.search(r"(?:=>\s+)?(/[A-Za-z0-9_+.,/@=-]+)", line)
        if matched is not None:
            dependency = Path(matched.group(1))
            if dependency.exists():
                dependencies.add(dependency)
    return tuple(sorted(dependencies, key=str))


def _copy_executable(runtime: Path, source: Path, destination: str) -> None:
    resolved = source.resolve(strict=True)
    _copy_regular(resolved, runtime / destination.lstrip("/"))
    for dependency in _dynamic_dependencies(resolved):
        _copy_regular(
            dependency,
            runtime / str(dependency).lstrip("/"),
        )


def _device(path: Path, major: int, minor: int, mode: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    os.mknod(path, stat.S_IFCHR | mode, os.makedev(major, minor))


def _validate_minimal_proc_self_exe(runtime: Path) -> None:
    """Validate the non-mounted ``current_exe`` shim used by native Codex.

    Rust resolves ``std::env::current_exe()`` through ``/proc/self/exe`` on
    Linux.  Mounting procfs would expose process and host-runtime information
    inside the blind-search chroot, so the v3 backend provides exactly one
    root-owned symlink instead.  Its target is the already launch-hash-bound
    Codex binary copied into the otherwise private chroot.
    """

    root = Path(runtime)
    if root.is_symlink() or not root.is_dir():
        raise RuntimeError("Codex chroot root is not a regular directory")
    proc = root / "proc"
    self_dir = proc / "self"
    executable_link = self_dir / "exe"
    for directory, label in ((proc, "/proc"), (self_dir, "/proc/self")):
        if directory.is_symlink() or not directory.is_dir():
            raise RuntimeError(f"Codex pseudo-proc {label} is not a directory")
        if stat.S_IMODE(directory.stat().st_mode) != 0o555:
            raise RuntimeError(f"Codex pseudo-proc {label} is not read-only")
        if directory.stat().st_uid != 0:
            raise RuntimeError(f"Codex pseudo-proc {label} is not root-owned")
    if os.path.ismount(proc):
        raise RuntimeError("Codex chroot must not mount procfs")
    if {entry.name for entry in proc.iterdir()} != {"self"}:
        raise RuntimeError("Codex pseudo-proc contains unexpected entries")
    if {entry.name for entry in self_dir.iterdir()} != {"exe"}:
        raise RuntimeError("Codex pseudo-proc/self contains unexpected entries")
    if (
        not executable_link.is_symlink()
        or os.readlink(executable_link) != _CHROOT_CODEX_PATH
        or executable_link.lstat().st_uid != 0
    ):
        raise RuntimeError("Codex pseudo-proc/self/exe binding changed")
    executable = root / _CHROOT_CODEX_PATH.lstrip("/")
    if (
        executable.is_symlink()
        or not executable.is_file()
        or executable.stat().st_uid != 0
        or stat.S_IMODE(executable.stat().st_mode) != 0o555
    ):
        raise RuntimeError("Codex chroot executable binding changed")


def _install_minimal_proc_self_exe(runtime: Path) -> None:
    """Install only ``/proc/self/exe``; never mount or copy host procfs."""

    proc = Path(runtime) / "proc"
    if proc.exists() or proc.is_symlink():
        raise RuntimeError("Codex chroot pseudo-proc already exists")
    self_dir = proc / "self"
    self_dir.mkdir(parents=True, mode=0o555)
    self_dir.chmod(0o555)
    proc.chmod(0o555)
    (self_dir / "exe").symlink_to(_CHROOT_CODEX_PATH)
    _validate_minimal_proc_self_exe(runtime)


def _isolated_codex_environment() -> dict[str, str]:
    """Return the complete deterministic environment for blind generation."""

    return dict(_CHROOT_CODEX_ENVIRONMENT)


def _isolated_codex_config_arguments() -> list[str]:
    """Disable supported tool surfaces at the CLI's highest precedence.

    The v3 runtime additionally omits every code-mode host and sandbox helper,
    so model-mandated executor calls fail closed rather than reaching a shell.
    """

    return [
        argument
        for override in _CHROOT_CODEX_CONFIG_OVERRIDES
        for argument in ("--config", override)
    ]


def _materialize_chroot_runtime(
    runtime: Path,
    *,
    codex_executable: Path,
    view: Path,
) -> Path:
    """Create a minimal filesystem with no mount or path to the main repo."""

    from evolve.ansatz_v3_codex_view import validate_sanitized_codex_view

    runtime.chmod(0o755)
    validate_sanitized_codex_view(PROJECT_ROOT, view)
    _copy_executable(runtime, codex_executable, _CHROOT_CODEX_PATH)
    tools = (
        (Path("/bin/bash"), "/bin/bash"),
        (Path("/bin/dash"), "/bin/dash"),
        (Path("/usr/bin/cat"), "/usr/bin/cat"),
        (Path("/usr/bin/find"), "/usr/bin/find"),
        (Path("/usr/bin/head"), "/usr/bin/head"),
        (Path("/usr/bin/ls"), "/usr/bin/ls"),
        (Path("/usr/bin/pwd"), "/usr/bin/pwd"),
        (Path("/usr/bin/rg"), "/usr/bin/rg"),
        (Path("/usr/bin/sed"), "/usr/bin/sed"),
        (Path("/usr/bin/sha256sum"), "/usr/bin/sha256sum"),
        (Path("/usr/bin/stat"), "/usr/bin/stat"),
        (Path("/usr/bin/tail"), "/usr/bin/tail"),
    )
    for source, destination in tools:
        _copy_executable(runtime, source, destination)
    (runtime / "bin/sh").symlink_to("dash")

    workspace = runtime / "workspace"
    shutil.copytree(view, workspace, symlinks=False)
    for root, directories, files in os.walk(workspace, topdown=False):
        for name in files:
            (Path(root) / name).chmod(0o444)
        for name in directories:
            (Path(root) / name).chmod(0o555)
    workspace.chmod(0o555)

    for relative in (
        "etc/hosts",
        "etc/nsswitch.conf",
        "etc/resolv.conf",
        "etc/ssl/certs/ca-certificates.crt",
    ):
        source = Path("/") / relative
        if source.is_file() and not source.is_symlink():
            _copy_regular(source, runtime / relative, mode=0o444)
    (runtime / "etc").mkdir(parents=True, exist_ok=True)
    (runtime / "etc/passwd").write_text(
        "nobody:x:65534:65534:ansatz-v3-codex:/nonexistent:/bin/sh\n",
        encoding="utf-8",
    )
    (runtime / "etc/group").write_text("nogroup:x:65534:\n", encoding="utf-8")
    (runtime / "etc/passwd").chmod(0o444)
    (runtime / "etc/group").chmod(0o444)

    auth_home = Path(os.environ.get("CODEX_HOME", Path.home() / ".codex"))
    auth_source = auth_home / "auth.json"
    auth_destination = runtime / "root/.codex/auth.json"
    _copy_regular(auth_source, auth_destination, mode=0o600)
    os.chown(auth_destination, _CHROOT_USER, _CHROOT_USER)
    for directory in (runtime / "root", runtime / "root/.codex"):
        os.chown(directory, _CHROOT_USER, _CHROOT_USER)
        directory.chmod(0o700)

    temporary = runtime / "tmp"
    temporary.mkdir(mode=0o1777)
    _install_minimal_proc_self_exe(runtime)
    _device(runtime / "dev/null", 1, 3, 0o666)
    _device(runtime / "dev/zero", 1, 5, 0o666)
    _device(runtime / "dev/random", 1, 8, 0o444)
    _device(runtime / "dev/urandom", 1, 9, 0o444)
    return workspace


def render_prompt(system_message: str, messages: list[dict[str, str]]) -> str:
    chunks = [
        "You are the text-generation backend for OpenEvolve. Do not edit files. "
        "Return only the response requested by the evolutionary prompt.",
        "",
        "## System message",
        system_message,
    ]
    for message in messages:
        role = str(message.get("role", "user")).upper()
        chunks.extend(["", f"## {role}", str(message.get("content", ""))])
    return "\n".join(chunks).strip() + "\n"


class CodexCliLLM:
    """Duck-typed OpenEvolve LLMInterface implemented with ``codex exec``."""

    def __init__(self, model_cfg: Any):
        self.model = model_cfg.name
        self.system_message = model_cfg.system_message or ""
        self.reasoning_effort = getattr(model_cfg, "reasoning_effort", None) or "xhigh"
        self.timeout = int(getattr(model_cfg, "timeout", None) or 900)
        self.retries = int(getattr(model_cfg, "retries", None) or 0)
        self.retry_delay = int(getattr(model_cfg, "retry_delay", None) or 5)
        self.codex_bin = os.environ.get("QCODE_CODEX_BIN", "codex")
        self.cwd = Path(os.environ.get("QCODE_CODEX_CWD", PROJECT_ROOT)).resolve()
        view_fields = {
            _ISOLATED_VIEW_ENV: os.environ.get(_ISOLATED_VIEW_ENV),
            _ISOLATED_VIEW_SHA_ENV: os.environ.get(_ISOLATED_VIEW_SHA_ENV),
            _ISOLATED_SOURCE_SHA_ENV: os.environ.get(_ISOLATED_SOURCE_SHA_ENV),
            _ISOLATED_BOUNDARY_ENV: os.environ.get(_ISOLATED_BOUNDARY_ENV),
        }
        present = {name for name, value in view_fields.items() if value is not None}
        if present and present != set(view_fields):
            raise RuntimeError("ansatz-v3 Codex view environment is incomplete")
        self.sanitized_view: dict[str, Any] | None = None
        if present:
            from evolve.ansatz_v3_codex_view import (
                validate_sanitized_codex_view,
            )

            manifest_path = Path(str(view_fields[_ISOLATED_VIEW_ENV])).resolve()
            if manifest_path.parent != self.cwd:
                raise RuntimeError("ansatz-v3 Codex manifest is outside its view")
            view = validate_sanitized_codex_view(PROJECT_ROOT, self.cwd)
            if (
                view["manifest_path"] != str(manifest_path)
                or view["manifest_file_sha256"]
                != view_fields[_ISOLATED_VIEW_SHA_ENV]
                or view["source_fingerprint_sha256"]
                != view_fields[_ISOLATED_SOURCE_SHA_ENV]
                or view["filesystem_boundary"]
                != view_fields[_ISOLATED_BOUNDARY_ENV]
            ):
                raise RuntimeError("ansatz-v3 Codex view binding changed")
            self.sanitized_view = view

    async def generate(self, prompt: str, **kwargs: Any) -> str:
        return await self.generate_with_context(
            self.system_message,
            [{"role": "user", "content": prompt}],
            **kwargs,
        )

    async def generate_with_context(
        self,
        system_message: str,
        messages: list[dict[str, str]],
        **kwargs: Any,
    ) -> str:
        prompt = render_prompt(system_message, messages)
        timeout = int(kwargs.get("timeout", self.timeout) or self.timeout)
        retries = int(kwargs.get("retries", self.retries) or 0)
        last_error = "unknown Codex CLI failure"
        for attempt in range(retries + 1):
            try:
                return await self._invoke(prompt, timeout)
            except (RuntimeError, asyncio.TimeoutError) as exc:
                last_error = str(exc)
                if attempt < retries:
                    await asyncio.sleep(self.retry_delay)
        raise RuntimeError(last_error)

    async def _invoke(self, prompt: str, timeout: int) -> str:
        runtime: Path | None = None
        output_dir: Path
        command_prefix: list[str]
        codex_path = self.codex_bin
        codex_cwd = str(self.cwd)
        output_argument: str
        child_environment: dict[str, str] | None = None
        if self.sanitized_view is None:
            output_dir = Path(tempfile.mkdtemp(prefix="qcode-codex-"))
            output_path = output_dir / "response.txt"
            output_argument = str(output_path)
            command_prefix = []
        else:
            chroot = shutil.which("chroot")
            if chroot is None or os.geteuid() != 0:
                raise RuntimeError(
                    "ansatz-v3 Codex isolation requires root chroot support"
                )
            runtime = Path(tempfile.mkdtemp(prefix="qcode-ansatz-v3-chroot-"))
            _materialize_chroot_runtime(
                runtime,
                codex_executable=Path(self.codex_bin),
                view=self.cwd,
            )
            _validate_minimal_proc_self_exe(runtime)
            output_dir = runtime / "tmp/qcode-codex-output"
            output_dir.mkdir(mode=0o700)
            os.chown(output_dir, _CHROOT_USER, _CHROOT_USER)
            output_path = output_dir / "response.txt"
            output_argument = "/tmp/qcode-codex-output/response.txt"
            codex_path = _CHROOT_CODEX_PATH
            codex_cwd = "/workspace"
            command_prefix = [
                chroot,
                f"--userspec={_CHROOT_USER}:{_CHROOT_USER}",
                str(runtime),
            ]
            child_environment = _isolated_codex_environment()
        command = [
            *command_prefix,
            codex_path,
            "exec",
            "--model", self.model,
            "--config", f'model_reasoning_effort="{self.reasoning_effort}"',
            *(
                _isolated_codex_config_arguments()
                if self.sanitized_view is not None
                else ()
            ),
            "--sandbox", "read-only",
            "--ephemeral",
            "--ignore-user-config",
            "--ignore-rules",
            "--skip-git-repo-check",
            "--color", "never",
            "--cd", codex_cwd,
            "--output-last-message", output_argument,
            "-",
        ]
        process = await asyncio.create_subprocess_exec(
            *command,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.DEVNULL,
            stderr=asyncio.subprocess.PIPE,
            env=child_environment,
        )
        try:
            _, stderr = await asyncio.wait_for(
                process.communicate(prompt.encode()), timeout=timeout
            )
        except asyncio.TimeoutError:
            process.kill()
            await process.wait()
            raise asyncio.TimeoutError(
                f"Codex CLI timed out after {timeout}s for model {self.model}"
            )
        try:
            if process.returncode != 0:
                detail = stderr.decode(errors="replace")[-4000:]
                raise RuntimeError(
                    f"Codex CLI exited {process.returncode} for {self.model}: {detail}"
                )
            if not output_path.is_file():
                raise RuntimeError("Codex CLI produced no output-last-message file")
            response = output_path.read_text().strip()
            if not response:
                raise RuntimeError("Codex CLI produced an empty response")
            return response
        finally:
            try:
                if runtime is None:
                    output_path.unlink(missing_ok=True)
                    output_dir.rmdir()
                else:
                    shutil.rmtree(runtime)
            except OSError:
                pass


def make_codex_cli_client(model_cfg: Any) -> CodexCliLLM:
    """Factory matching OpenEvolve's ``LLMModelConfig.init_client`` contract."""
    return CodexCliLLM(model_cfg)
