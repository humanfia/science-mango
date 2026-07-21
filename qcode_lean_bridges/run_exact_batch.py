#!/usr/bin/env python3
"""Generate and compile exact [[n,k,d]] Lean certificates with resume state."""
from __future__ import annotations
import argparse, concurrent.futures, hashlib, os, subprocess, sys, time
from pathlib import Path


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


def compile_one(out: Path, source: Path, state: Path) -> tuple[str, bool, str, float]:
    name = source.stem
    source_hash = digest(source)
    ok_file = state / 'ok' / name
    olean = source.with_suffix('.olean')
    if ok_file.exists() and olean.exists() and ok_file.read_text().strip() == source_hash:
        return name, True, 'cached', 0.0
    log = state / 'logs' / f'{name}.log'
    started = time.monotonic()
    env = os.environ.copy()
    env['LEAN_PATH'] = str(out) + (':' + env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    with log.open('w') as stream:
        proc = subprocess.run(['lake', 'env', 'lean', '-o', str(olean), str(source)],
            cwd=out, env=env, stdout=stream, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - started
    if proc.returncode == 0:
        ok_file.write_text(source_hash + '\n')
        (state / 'failed' / name).unlink(missing_ok=True)
        return name, True, 'built', elapsed
    (state / 'failed' / name).write_text(f'{source_hash} {proc.returncode}\n')
    return name, False, f'exit={proc.returncode}', elapsed


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--catalog', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--seed-witnesses', type=Path)
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--search-timeout', type=int, default=10800)
    ap.add_argument('--sat-timeout', type=int, default=10800)
    ap.add_argument('--generator', type=Path,
        default=Path(__file__).with_name('bridge_exact.py'))
    args = ap.parse_args()
    if not 1 <= args.jobs <= 4:
        ap.error('--jobs must be between 1 and 4 (each Lean worker can use 6-7 GB)')
    out = args.out.resolve(); out.mkdir(parents=True, exist_ok=True)
    state = out / '.exact-state'
    for stale in (state / 'generator.exit', state / 'batch.exit'):
        stale.unlink(missing_ok=True)
    for sub in ('ok', 'failed', 'logs'):
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
            stdout=gen_log, stderr=subprocess.STDOUT)
        (state / 'generator.pid').write_text(str(generator.pid) + '\n')
        attempted: set[str] = set()
        running: dict[concurrent.futures.Future, Path] = {}
        failures = 0
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while True:
                for future in list(running):
                    if not future.done():
                        continue
                    source = running.pop(future)
                    name, ok, status, elapsed = future.result()
                    print(f'{name}: {status} ({elapsed:.1f}s)', flush=True)
                    failures += 0 if ok else 1
                basic = out / 'QExact' / 'Basic.lean'
                basic_ok = False
                if stable(basic):
                    name, ok, status, elapsed = compile_one(out, basic, state)
                    basic_ok = ok
                    if status != 'cached':
                        print(f'{name}: {status} ({elapsed:.1f}s)', flush=True)
                    if not ok:
                        generator.wait()
                        (state / 'generator.exit').write_text(str(generator.returncode) + '\n')
                        return 1
                if basic_ok:
                    sources = sorted((out / 'QExact').glob('Code_*.lean'))
                    for source in sources:
                        if len(running) >= args.jobs:
                            break
                        if source.name in attempted or not stable(source):
                            continue
                        attempted.add(source.name)
                        running[pool.submit(compile_one, out, source, state)] = source
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
        (state / 'generator.exit').write_text(str(generator.returncode) + '\n')
        (state / 'batch.exit').write_text(str(0 if generator.returncode == 0 and failures == 0 else 1) + '\n')
        print(f'generator exit={generator.returncode}; compile failures={failures}', flush=True)
        return 0 if generator.returncode == 0 and failures == 0 else 1

if __name__ == '__main__':
    raise SystemExit(main())
