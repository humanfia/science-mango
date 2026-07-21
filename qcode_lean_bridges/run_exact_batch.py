#!/usr/bin/env python3
"""Generate and compile exact [[n,k,d]] Lean certificates with resume state."""
from __future__ import annotations
import argparse, concurrent.futures, hashlib, os, re, signal, subprocess, sys, threading, time
from pathlib import Path

GIB = 1024 ** 3
_STOP = threading.Event()
_ACTIVE_LOCK = threading.Lock()
_ACTIVE: set[subprocess.Popen] = set()


def cgroup_memory() -> tuple[int, int] | None:
    """Return (limit, current) for cgroup v2, or None without a finite limit."""
    root = Path('/sys/fs/cgroup')
    try:
        raw_limit = (root / 'memory.max').read_text().strip()
        if raw_limit == 'max':
            return None
        return int(raw_limit), int((root / 'memory.current').read_text().strip())
    except (FileNotFoundError, ValueError, OSError):
        return None


def memory_allows_start(reserve_gib: float, per_job_gib: float,
        active_jobs: int = 0) -> bool:
    """Keep enough cgroup headroom for existing workers and unrelated jobs."""
    if per_job_gib <= 0:
        return True
    usage = cgroup_memory()
    if usage is None:
        return True
    limit, current = usage
    launch_budget = int((active_jobs + 1) * per_job_gib * GIB)
    return current + launch_budget <= limit - int(reserve_gib * GIB)


def source_priority(path: Path) -> tuple[int, int, int, str]:
    """Run smaller expected SAT instances first for faster verified throughput."""
    match = re.match(r'Code_(\d+)_(\d+)_(\d+)', path.stem)
    if match is None:
        return (sys.maxsize, sys.maxsize, sys.maxsize, path.name)
    n, _k, d = map(int, match.groups())
    return (n * d, n, d, path.name)


def terminate_tree(proc: subprocess.Popen, sig: signal.Signals = signal.SIGTERM) -> None:
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, sig)
    except ProcessLookupError:
        pass


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def stable(path: Path, seconds: float = 2.0) -> bool:
    try:
        return time.time() - path.stat().st_mtime >= seconds
    except FileNotFoundError:
        return False


def cache_hit(source: Path, state: Path) -> bool:
    name = source.stem
    ok_file = state / 'ok' / name
    olean = source.with_suffix('.olean')
    return (ok_file.exists() and olean.exists() and
        ok_file.read_text().strip() == digest(source))


def compile_one(out: Path, source: Path, state: Path,
        lean_memory_mib: int = 0) -> tuple[str, bool, str, float]:
    name = source.stem
    source_hash = digest(source)
    ok_file = state / 'ok' / name
    olean = source.with_suffix('.olean')
    if ok_file.exists() and olean.exists() and ok_file.read_text().strip() == source_hash:
        return name, True, 'cached', 0.0
    log = state / 'logs' / f'{name}.log'
    tmp_olean = state / 'tmp' / f'{name}.{os.getpid()}.{threading.get_ident()}.olean'
    tmp_olean.unlink(missing_ok=True)
    started = time.monotonic()
    env = os.environ.copy()
    env['LEAN_PATH'] = str(out) + (':' + env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    command = ['lake', 'env', 'lean']
    if lean_memory_mib > 0:
        command += ['-M', str(lean_memory_mib)]
    command += ['-o', str(tmp_olean), str(source)]
    with log.open('w') as stream:
        proc = subprocess.Popen(command, cwd=out, env=env, stdout=stream,
            stderr=subprocess.STDOUT, start_new_session=True)
        with _ACTIVE_LOCK:
            _ACTIVE.add(proc)
        try:
            returncode = proc.wait()
        finally:
            with _ACTIVE_LOCK:
                _ACTIVE.discard(proc)
    elapsed = time.monotonic() - started
    if returncode == 0 and tmp_olean.exists():
        os.replace(tmp_olean, olean)
        ok_file.write_text(source_hash + '\n')
        (state / 'failed' / name).unlink(missing_ok=True)
        return name, True, 'built', elapsed
    tmp_olean.unlink(missing_ok=True)
    (state / 'failed' / name).write_text(f'{source_hash} {returncode}\n')
    status = 'stopped' if _STOP.is_set() else f'exit={returncode}'
    return name, False, status, elapsed


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--catalog', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--seed-witnesses', type=Path)
    ap.add_argument('--jobs', type=int, default=4,
        help='Maximum workers; the memory gate may temporarily use fewer')
    ap.add_argument('--memory-reserve-gib', type=float, default=16,
        help='Cgroup memory kept free for spikes and unrelated jobs')
    ap.add_argument('--memory-per-job-gib', type=float, default=8,
        help='Headroom required before another Lean worker; 0 disables gate')
    ap.add_argument('--lean-memory-mib', type=int, default=0,
        help='Optional per-Lean -M limit in MiB; 0 leaves it unlimited')
    ap.add_argument('--search-timeout', type=int, default=10800)
    ap.add_argument('--sat-timeout', type=int, default=10800)
    ap.add_argument('--generator', type=Path,
        default=Path(__file__).with_name('bridge_exact.py'))
    args = ap.parse_args()
    if not 1 <= args.jobs <= 16:
        ap.error('--jobs must be between 1 and 16')
    out = args.out.resolve(); out.mkdir(parents=True, exist_ok=True)
    state = out / '.exact-state'
    for stale in (state / 'generator.exit', state / 'batch.exit'):
        stale.unlink(missing_ok=True)
    for sub in ('ok', 'failed', 'logs', 'tmp'):
        (state / sub).mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, str(args.generator.resolve()), '--catalog', str(args.catalog.resolve()),
        '--out', str(out), '--search-timeout', str(args.search_timeout),
        '--sat-timeout', str(args.sat_timeout)]
    if args.seed_witnesses:
        cmd += ['--seed-witnesses', str(args.seed_witnesses.resolve())]
    with (out / 'generator.log').open('a') as gen_log:
        gen_log.write(f'\n=== run {time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime())} ===\n')
        gen_log.flush()
        generator = subprocess.Popen(cmd, cwd=args.generator.resolve().parent,
            stdout=gen_log, stderr=subprocess.STDOUT, start_new_session=True)
        (state / 'generator.pid').write_text(str(generator.pid) + '\n')

        def request_stop(signum, _frame) -> None:
            if _STOP.is_set():
                return
            print(f'received signal {signum}; stopping generator and Lean workers', flush=True)
            _STOP.set()
            terminate_tree(generator)
            with _ACTIVE_LOCK:
                workers = list(_ACTIVE)
            for worker in workers:
                terminate_tree(worker)

        signal.signal(signal.SIGTERM, request_stop)
        signal.signal(signal.SIGINT, request_stop)
        attempted: set[str] = set()
        running: dict[concurrent.futures.Future, Path] = {}
        failures = 0
        last_memory_notice = 0.0
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while True:
                for future in list(running):
                    if not future.done():
                        continue
                    source = running.pop(future)
                    name, ok, status, elapsed = future.result()
                    print(f'{name}: {status} ({elapsed:.1f}s)', flush=True)
                    failures += 0 if ok else 1
                if _STOP.is_set():
                    if not running:
                        break
                    time.sleep(0.2)
                    continue
                basic = out / 'QExact' / 'Basic.lean'
                basic_ok = False
                if stable(basic):
                    name, ok, status, elapsed = compile_one(
                        out, basic, state, args.lean_memory_mib)
                    basic_ok = ok
                    if status != 'cached':
                        print(f'{name}: {status} ({elapsed:.1f}s)', flush=True)
                    if not ok:
                        generator.wait()
                        (state / 'generator.exit').write_text(str(generator.returncode) + '\n')
                        return 1
                if basic_ok:
                    sources = sorted((out / 'QExact').glob('Code_*.lean'), key=source_priority)
                    for source in sources:
                        if len(running) >= args.jobs:
                            break
                        if source.name in attempted or not stable(source):
                            continue
                        if not cache_hit(source, state) and not memory_allows_start(
                                args.memory_reserve_gib, args.memory_per_job_gib, len(running)):
                            now = time.monotonic()
                            if now - last_memory_notice >= 60:
                                usage = cgroup_memory()
                                detail = '' if usage is None else (
                                    f' ({usage[1] / GIB:.1f}/{usage[0] / GIB:.1f} GiB used)')
                                print(f'memory gate: waiting before next Lean worker{detail}',
                                    flush=True)
                                last_memory_notice = now
                            break
                        attempted.add(source.name)
                        running[pool.submit(compile_one, out, source, state,
                            args.lean_memory_mib)] = source
                gen_done = generator.poll() is not None
                if gen_done and not running:
                    # One last scan catches modules emitted immediately before exit.
                    pending = [p for p in sorted((out / 'QExact').glob('Code_*.lean'))
                        if p.name not in attempted]
                    if pending:
                        time.sleep(2.1)
                        continue
                    break
                time.sleep(2)
        if _STOP.is_set():
            terminate_tree(generator)
            try:
                generator.wait(timeout=5)
            except subprocess.TimeoutExpired:
                terminate_tree(generator, signal.SIGKILL)
                generator.wait()
            (state / 'generator.exit').write_text(str(generator.returncode) + '\n')
            (state / 'batch.exit').write_text('130\n')
            return 130
        (state / 'generator.exit').write_text(str(generator.returncode) + '\n')
        (state / 'batch.exit').write_text(str(0 if generator.returncode == 0 and failures == 0 else 1) + '\n')
        print(f'generator exit={generator.returncode}; compile failures={failures}', flush=True)
        return 0 if generator.returncode == 0 and failures == 0 else 1

if __name__ == '__main__':
    raise SystemExit(main())
