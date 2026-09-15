"""Prepare or launch a frozen dependency-aware Lean experiment."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from .dag_runner import load_graph
from .engine import fingerprint, save


def add_parser(commands):
    p = commands.add_parser('formalize-dag', help='Run ready Lean proof nodes with up to 16 concurrent workers')
    p.add_argument('--project', required=True, type=Path)
    p.add_argument('--graph', required=True, type=Path)
    p.add_argument('--concurrency', type=int, choices=range(1,17), default=16)
    p.add_argument('--rounds', type=int, choices=range(1,21), default=5)
    p.add_argument('--compile-timeout', type=int, default=180)
    p.add_argument('--turn-timeout', type=int, default=600)
    p.add_argument('--model', default='gpt-6-astra')
    p.add_argument('--effort', default='medium')
    p.add_argument('--live', action='store_true')
    return p


def launch(args):
    from pipelines.quantum_humanize._runtime import runtime_pin
    runtime_pin()
    graph, nodes = load_graph(args.graph)
    project = args.project.resolve(strict=True)
    fingerprint(project)
    if any(c in args.model+args.effort for c in ',\n\r\0'):
        raise ValueError('invalid model/effort')
    if not all(1 <= x <= 3600 for x in (args.compile_timeout,args.turn_timeout)):
        raise ValueError('timeouts must be in 1..3600')
    plan = {'project': str(project), 'concurrency': args.concurrency, 'rounds': args.rounds,
            'compile_timeout': args.compile_timeout, 'turn_timeout': args.turn_timeout}
    if not args.live:
        print(json.dumps({'status':'prepared_no_model_calls', **plan,
                          'executable_nodes':sum(n.spec is not None for n in nodes),
                          'planned_nodes':sum(n.spec is None for n in nodes),
                          'model':args.model,'effort':args.effort},indent=2))
        return 0
    hmz = Path(sys.executable).parent/'hmz'
    if not hmz.is_file():
        raise ValueError('use the pinned hmz Python environment')
    area = project/'.humanize-formal-runs'
    if area.is_symlink():
        raise ValueError('run area must not be symlink')
    area.mkdir(exist_ok=True)
    control = Path(tempfile.mkdtemp(prefix='dag-launcher-',dir=area))
    save(control/'graph.json',graph)
    plan.update(graph=str(control/'graph.json'),output=str(control/'experiment'),result_path=str(control/'result.json'))
    save(control/'config.json',plan)
    home=control/'humanize-home'
    home.mkdir()
    repo=Path(__file__).resolve().parents[2]
    env=dict(os.environ,HUMANIZE_HOME=str(home),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1')
    env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','')
    argv=[str(hmz),'exec','-f',str(repo/'pipelines/quantum_formalize_dag'),'-c',str(control/'config.json'),
          '-a',f'cli=codex,model={args.model},effort={args.effort},permission=read-only,web_search=false',
          'Prove the frozen Lean DAG nodes. Preserve the target and use both LeanExplore libraries.']
    print(json.dumps({'launcher':str(control),'concurrency':args.concurrency,'model':args.model,'effort':args.effort}),flush=True)
    run=subprocess.run(argv,cwd=control,env=env,check=False)
    if run.returncode:
        return run.returncode
    receipt=control/'result.json'
    if not receipt.is_file():
        return 1
    return int(not json.loads(receipt.read_text()).get('experiment_passed',False))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    add_parser(p.add_subparsers(dest='action',required=True))
    return launch(p.parse_args())


if __name__ == '__main__':
    raise SystemExit(main())
