"""Explicit live launch, or an offline description of the formalization command."""
import argparse
import asyncio
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile

from .engine import Spec, fingerprint, save
from .search import search_both


def add_parser(commands):
    parser = commands.add_parser('formalize', help='LeanExplore → Lean proof → compiler repair → acceptance')
    parser.add_argument('--project', required=True, type=Path)
    parser.add_argument('--spec', required=True, type=Path, help='Frozen declaration specification JSON')
    parser.add_argument('--model', default='gpt-6-astra')
    parser.add_argument('--effort', default='medium')
    parser.add_argument('--rounds', type=int, choices=range(1, 21), default=5)
    parser.add_argument('--compile-timeout', type=int, default=180)
    parser.add_argument('--turn-timeout', type=int, default=600)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--live', action='store_true')
    mode.add_argument('--search-only', action='store_true', help='Query both libraries without model turns')
    return parser


def launch(args):
    from pipelines.quantum_humanize._runtime import runtime_pin
    runtime_pin()
    project = args.project.resolve(strict=True)
    spec = Spec.model_validate_json(args.spec.read_bytes())
    fingerprint(project)
    if args.search_only:
        receipts = asyncio.run(search_both(spec.queries))
        print(json.dumps(receipts, ensure_ascii=False, indent=2))
        return int(any(x['status'] != 'ok' for x in receipts))
    if any(c in args.model + args.effort for c in ',\n\r\0'):
        raise ValueError('invalid model or effort')
    if not (1 <= args.compile_timeout <= 3600 and 1 <= args.turn_timeout <= 3600):
        raise ValueError('timeouts must be between 1 and 3600 seconds')
    hmz = Path(sys.executable).parent / 'hmz'
    if not hmz.is_file():
        raise ValueError('use the pinned Python environment with hmz installed beside Python')
    plan = {'project': str(project), 'spec': str(args.spec.resolve()),
            'max_rounds': args.rounds, 'compile_timeout': args.compile_timeout,
            'turn_timeout': args.turn_timeout}
    if not args.live:
        print(json.dumps({'status': 'prepared_no_model_calls', 'config': plan,
                          'libraries': {'Mathlib': 'Mathlib', 'Physlib': 'Physlib'},
                          'model': args.model, 'effort': args.effort}, indent=2))
        print('Add --live to run the proof loop or --search-only to test both libraries.')
        return 0
    area = project / '.humanize-formal-runs'
    if area.is_symlink():
        raise ValueError('formal run area must not be a symlink')
    area.mkdir(exist_ok=True)
    control = Path(tempfile.mkdtemp(prefix='launcher-', dir=area))
    save(control / 'spec.json', spec.model_dump())
    plan['spec'] = str(control / 'spec.json')
    plan['result_path'] = str(control / 'result.json')
    save(control / 'config.json', plan)
    home = control / 'humanize-home'
    home.mkdir()
    argv = [str(hmz), 'exec', '-f', str(Path(__file__).parent), '-c', str(control / 'config.json'),
            '-a', f'cli=codex,model={args.model},effort={args.effort},permission=read-only,web_search=false',
            'Formalize the exact frozen Lean target using both LeanExplore library searches.']
    print(shlex.join(argv), flush=True)
    env = dict(os.environ, HUMANIZE_HOME=str(home), HUMANIZE_SENTRY='off', PYTHONDONTWRITEBYTECODE='1')
    result = subprocess.run(argv, cwd=control, env=env, check=False)
    if result.returncode:
        return result.returncode
    receipt = control / 'result.json'
    if not receipt.is_file():
        print('Formalization ended without an acceptance receipt.', file=sys.stderr)
        return 1
    return int(not json.loads(receipt.read_text()).get('accepted', False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='action', required=True)
    add_parser(commands)
    return launch(parser.parse_args())


if __name__ == '__main__':
    raise SystemExit(main())
