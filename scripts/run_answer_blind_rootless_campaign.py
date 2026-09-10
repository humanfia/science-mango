#!/usr/bin/env python3
"""Run the native Archon chemistry lifecycle in an unprivileged mount namespace.

The repository, grader, prior results and host home are never mounted. This
provides filesystem/PID isolation, not network isolation or a separate-UID
trusted scoring boundary. All official-answer grading stays outside this run.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


PROTOCOL = "icho-full68-rootless-native-v1"
SCRIPTS = (
    "run_answer_blind_archon_campaign.py",
    "build_answer_blind_solver_seed.py",
    "configure_answer_blind_workspace.py",
)
PROTECTED = (
    "icho_2026_source", "reports/icho_2026", "isolation_manifest.json",
    "AGENTS.md", ".archon/config.json", "lakefile.toml", "lake-manifest.json",
    "lean-toolchain", "IChO2026Chem", "IChO2026Chem.lean",
    ".archon/AGENTS.md", "ANSWER_BLIND_PROTOCOL.md", ".archon/prompts",
    ".archon/prover-modes", ".mcp.json",
)


def save(path: Path, value: dict) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    os.replace(temporary, path)


def snapshot(source: Path, runtime: Path, python: Path) -> None:
    """Copy only engine and trusted generic launch code, never the checkout."""
    runtime.mkdir(parents=True, exist_ok=False)
    shutil.copytree(source / "src/archon", runtime / "src/archon",
                    ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    (runtime / "scripts").mkdir()
    for name in SCRIPTS:
        shutil.copy2(source / "scripts" / name, runtime / "scripts" / name)
    (runtime / "bin").mkdir()
    archon = runtime / "bin/archon"
    archon.write_text(f"#!{python}\nfrom archon.cli import app\napp()\n")
    archon.chmod(0o755)
    inventory = {
        str(path.relative_to(runtime)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(runtime.rglob("*")) if path.is_file()
    }
    save(runtime / "inventory.json", inventory)


def namespace(args, command: list[str], *, protected: bool = False) -> list[str]:
    runtime, campaign = args.runtime, args.campaign
    result = [str(args.bwrap), "--unshare-user", "--unshare-pid", "--unshare-ipc",
              "--unshare-uts", "--die-with-parent", "--new-session",
              "--cap-drop", "ALL", "--clearenv"]
    for path in ("/usr", "/lib", "/lib64"):
        if Path(path).exists():
            result += ["--ro-bind", path, path]
    result += ["--symlink", "usr/bin", "/bin", "--symlink", "usr/sbin", "/sbin",
               "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp"]
    for path in ("/etc/ssl", "/etc/resolv.conf", "/etc/hosts", "/etc/nsswitch.conf",
                 "/etc/passwd", "/etc/group", "/etc/localtime"):
        if Path(path).exists():
            result += ["--ro-bind", path, path]
    # The venv and its underlying interpreter have absolute paths. Mount only
    # those exact directories, leaving their repository/home ancestors empty.
    readonly = [runtime, args.seed, args.packages, args.lean_bin.parent,
                args.python.parent.parent, args.python.resolve().parent.parent]
    if args.python.is_symlink():
        target = Path(os.readlink(args.python))
        if not target.is_absolute():
            target = args.python.parent / target
        readonly.append(target.parent.parent)
    for path in dict.fromkeys(readonly):
        result += ["--ro-bind", str(path), str(path)]
    code_host = args.codex.parent / "codex-code-mode-host"
    if code_host.is_file():
        result += ["--ro-bind", str(code_host), "/tools/codex-code-mode-host"]
    result += ["--ro-bind", str(args.codex), "/tools/codex",
               "--bind", str(campaign), str(campaign),
               "--bind", str(args.private_home), "/home/solver"]
    if protected:
        for relative in PROTECTED:
            path = campaign / "workspace" / relative
            if path.exists():
                result += ["--ro-bind", str(path), str(path)]
    env = {
        "HOME": "/home/solver", "CODEX_HOME": "/home/solver/.codex",
        "PATH": f"{runtime}/bin:{args.lean_bin}:{args.python.parent}:/tools:/usr/bin:/bin",
        "PYTHONPATH": str(runtime / "src"), "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONUNBUFFERED": "1", "PYTHONNOUSERSITE": "1",
        "ARCHON_CODEX_BIN": "/tools/codex", "LANG": "C.UTF-8",
        "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null",
    }
    for key, value in env.items():
        result += ["--setenv", key, value]
    result += ["--chdir", str(campaign), "--", *command]
    return result


def native_command(args, *, resume=False) -> list[str]:
    result = [str(args.python), str(args.runtime / "scripts" / SCRIPTS[0]),
              "--campaign-root", str(args.campaign),
              "--lake-packages", str(args.packages), "--reuse-lake-packages",
              "--archon-bin", str(args.runtime / "bin/archon"),
              "--expected-items", "68", "--max-parallel", "32",
              "--max-iterations", "100", "--review-max-iterations", "10",
              "--target-lifecycle"]
    return result + (["--resume"] if resume else ["--seed-workspace", str(args.seed)])


def validate(args) -> None:
    if os.geteuid() == 0:
        raise ValueError("this launcher is for an unprivileged host account")
    for path in (args.campaign, args.private_home):
        if path in (Path('/'), Path.home()) or Path.home().is_relative_to(path):
            raise ValueError(f"refusing a broad writable mount: {path}")
        if args.source.is_relative_to(path) or path.is_relative_to(args.source):
            raise ValueError("campaign and private home must be outside the source checkout")
    for path in (args.runtime, args.seed, args.packages, args.lean_bin,
                 args.python.parent.parent, args.python.resolve().parent.parent):
        if not path.is_dir():
            raise ValueError(f"missing runtime directory: {path}")
        if path in (Path('/'), Path.home()) or Path.home().is_relative_to(path):
            raise ValueError(f"refusing a broad home/filesystem mount: {path}")
    for path in (args.bwrap, args.codex, args.python):
        if not path.is_file() or not os.access(path, os.X_OK):
            raise ValueError(f"missing executable: {path}")
    code_host = args.codex.parent / "codex-code-mode-host"
    if not code_host.is_file() or not os.access(code_host, os.X_OK):
        raise ValueError(f"missing Codex companion executable: {code_host}")
    if args.private_home == args.campaign or args.private_home.is_relative_to(args.campaign):
        raise ValueError("private home must be separate from campaign")
    for mount in (args.runtime, args.seed, args.packages):
        if args.source.is_relative_to(mount) or mount == args.source:
            raise ValueError("repository may not be exposed to the solver")
    rows = [json.loads(line) for line in (args.seed / 'icho_2026_source/questions_only.jsonl').read_text().splitlines() if line]
    expected = {f'icho_2026_t{q}_a{p}' for q, n in enumerate((6,7,7,9,6,7,7,10,9), 1) for p in range(1,n+1)}
    if len(rows) != 68 or {r['id'] for r in rows} != expected or any(r.get('official_answer_seen') is not False for r in rows):
        raise ValueError("seed is not the exact answer-blind full68 scope")


def supervise(args) -> int:
    lock_path = args.campaign.parent / (args.campaign.name + '.rootless.lock')
    campaign_lock = lock_path.open('a')
    fcntl.flock(campaign_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    status_file = args.campaign.parent / (args.campaign.name + '.rootless.json')
    status = dict(protocol=PROTOCOL, pid=os.getpid(), model='gpt-5.6-sol', effort='max',
                  targets=68, concurrency=32, network_isolated=False,
                  filesystem_isolated=True, separate_uid_verifier=False,
                  campaign=str(args.campaign), status='preflight', started=time.time())
    save(status_file, status)
    try:
        # Probe visibility before any model is started. Also check fresh PID
        # namespace and the effective UID; no host process root is available.
        probe = ['sh', '-c', 'test "$(id -u)" != 0 && test ! -e "$1" && test ! -e "$2" && echo ROOTLESS_ISOLATION_OK',
                 'probe', str(args.source), str(Path.home() / '.codex/auth.json')]
        subprocess.run(namespace(args, probe), check=True)
        if not (args.campaign / 'campaign.json').exists():
            status['status'] = 'preparing'
            save(status_file, status)
            subprocess.run(namespace(args, native_command(args)), check=True)
        config_path = args.campaign / 'workspace/.archon/config.json'
        config = json.loads(config_path.read_text())
        config['loop']['rootless_full_theory'] = True
        save(config_path, config)
        policy = args.campaign / 'workspace/AGENTS.md'
        if not policy.exists() or 'Rootless full-theory derivation policy' not in policy.read_text():
            with policy.open('a') as stream:
                stream.write('\n## Rootless full-theory derivation policy\n\n'
                             'This fresh full68 run has no certified prior-run results. '
                             'Derive all needed previous-part results from the bound problem '
                             'statements and figures, including A4/A5 facts needed by A6. '
                             'Do not assume a requested answer or treat an unsupported prior result '
                             'as a hypothesis. All semantic_requirements in each output contract '
                             'are mandatory source-to-Lean and independent-review obligations.\n')
        contract_probe = (
            'import json; from pathlib import Path; '
            'from archon.commands.loop.problem_only_review_contract import resolve_native_formalizer_source_contract; '
            'from archon.commands.loop.native_semantic_review import build_native_semantic_review_contract; '
            'from archon.commands.loop.native_semantic_review import _trusted_pinned_environment, _verified_pinned_library_declarations; '
            f'p=Path({str(args.campaign / "workspace")!r}); '
            'rows=[json.loads(line) for line in (p/"icho_2026_source/questions_only.jsonl").read_text().splitlines() if line]; '
            'targets=[p/"IChO2026Problems"/("problem_"+row["id"]+".lean") for row in rows]; '
            'assert len(targets)==68; '
            '[resolve_native_formalizer_source_contract(project_path=p,target=t) for t in targets]; '
            'reviews=[build_native_semantic_review_contract(project_path=p,target=t) for t in targets]; '
            'assert all(r and r["valid"] for r in reviews), [r for r in reviews if not r or not r["valid"]]; '
            'packages=("Mathlib","Physlib","CRNT"); '
            'assert _trusted_pinned_environment(p,packages) is not None, "pinned runtime is not sealed"; '
            'samples=[(("Mathlib",),{"Real.hasDerivAt_exp"}),(("Physlib",),{"WithDim.withDim_hMul_val"}),(("CRNT",),{"CRNT.Reaction.vector"})]; '
            'verified=[_verified_pinned_library_declarations(p,pkgs,refs) for pkgs,refs in samples]; '
            'assert all(found==refs for found,(_,refs) in zip(verified,samples)), ("pinned origin probe", [sorted(v) for v in verified]); '
            'print("FULL68_NATIVE_CONTRACTS_OK")'
        )
        subprocess.run(namespace(args, [str(args.python), '-c', contract_probe], protected=True), check=True)
        status['status'] = 'running'
        save(status_file, status)
        child = subprocess.Popen(namespace(args, native_command(args, resume=True), protected=True))
        status['child_pid'] = child.pid
        save(status_file, status)
        code = child.wait()
        index = json.loads((args.campaign / 'campaign.json').read_text())
        status.update(status=index.get('status', 'failed') if code == 0 else 'failed',
                      returncode=code, finished=time.time())
        save(status_file, status)
        return code
    except Exception as exc:
        status.update(status='failed', error=str(exc), finished=time.time())
        save(status_file, status)
        raise
    finally:
        campaign_lock.close()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('source', 'runtime', 'seed', 'packages', 'campaign', 'private-home',
                 'python', 'lean-bin', 'codex', 'bwrap'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--auth-file', type=Path)
    parser.add_argument('--snapshot', action='store_true')
    parser.add_argument('--detach', action='store_true')
    parser.add_argument('--preflight', action='store_true', help='test namespace and native CLI without preparing or calling models')
    args = parser.parse_args()
    for name in ('source', 'runtime', 'seed', 'packages', 'campaign', 'private_home', 'lean_bin', 'codex', 'bwrap'):
        setattr(args, name, getattr(args, name).resolve())
    args.python = args.python.absolute()  # preserve virtual-environment prefix
    if args.snapshot:
        snapshot(args.source, args.runtime, args.python)
    validate(args)
    args.campaign.mkdir(parents=True, exist_ok=True)
    args.private_home.mkdir(parents=True, exist_ok=True, mode=0o700)
    if args.auth_file:
        auth_dir = args.private_home / '.codex'
        auth_dir.mkdir(mode=0o700, exist_ok=True)
        shutil.copyfile(args.auth_file, auth_dir / 'auth.json')
        (auth_dir / 'auth.json').chmod(0o600)
    if not (args.private_home / '.codex/auth.json').is_file():
        raise ValueError('experiment-specific Codex authentication is missing')
    if args.preflight:
        subprocess.run(namespace(args, [str(args.runtime / 'bin/archon'), 'chemistry-constant', 'atomic_weight', 'C']), check=True)
        subprocess.run(namespace(args, [str(args.lean_bin / 'lean'), '--version']), check=True)
        subprocess.run(namespace(args, native_command(args) + ['--dry-run']), check=True)
        print(json.dumps({'status': 'preflight_passed', 'model': 'gpt-5.6-sol', 'targets': 68, 'concurrency': 32}))
        return 0
    if args.detach:
        command = [sys.executable, str(Path(__file__).resolve())]
        for name in ('source', 'runtime', 'seed', 'packages', 'campaign', 'private_home', 'python', 'lean_bin', 'codex', 'bwrap'):
            command += ['--' + name.replace('_', '-'), str(getattr(args, name))]
        log_path = args.campaign.parent / (args.campaign.name + '.launcher.log')
        with log_path.open('a') as log:
            child = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=log,
                                     stderr=subprocess.STDOUT, start_new_session=True, close_fds=True)
        print(json.dumps(dict(pid=child.pid, log=str(log_path), status='starting')))
        return 0
    return supervise(args)


if __name__ == '__main__':
    raise SystemExit(main())
