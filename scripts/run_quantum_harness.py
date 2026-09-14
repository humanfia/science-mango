"""Launch the quantum harness against an explicitly selected research checkout."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
def main():
    p=argparse.ArgumentParser()
    p.add_argument('--repo', type=Path, required=True, help='Quantum research checkout containing the roadmap and baseline checker')
    mode=p.add_mutually_exclusive_group()
    mode.add_argument('--live',action='store_true')
    mode.add_argument('--prepare',action='store_true')
    p.add_argument('--obligation',choices=['self_audit','birth_lift','distance_law','selector'],default='self_audit')
    p.add_argument('--model',default='gpt-6-astra')
    p.add_argument('--effort',default='medium')
    p.add_argument('--audit-input', action='append', default=[])
    p.add_argument('--rounds', type=int, default=20)
    p.add_argument('--audit-only', action='store_true')
    a=p.parse_args()
    research_root=a.repo.expanduser().resolve()
    if not research_root.is_dir():
        p.error('--repo must name an existing research checkout')
    if a.audit_only and not a.audit_input:
        p.error('--audit-only requires --audit-input')
    cmd=[sys.executable,'-m','pipelines.quantum_humanize','prepare' if a.prepare else 'launch','--repo',str(research_root),'--obligation',a.obligation]
    for directory in ['docs','scripts','tests','evidence','data']:
        for file in sorted((research_root/directory).iterdir()):
            if file.is_file() and file.suffix in {'.md','.py','.json','.jsonl','.csv'}:
                cmd.extend(['--extra-input',str(file.relative_to(research_root))])
    if a.prepare:
        cmd.append('--checks')
    else:
        cmd.extend(['--model',a.model,'--effort',a.effort,'--parallelism','4',
                    '--attempts','1' if a.audit_input else '4','--rounds',str(a.rounds),
                    '--max-calls','640','--no-coverage-planning',
                    '--turn-timeout-seconds','3600','--audit-continuations','4'])
        for seed in a.audit_input:
            cmd.extend(['--audit-input', seed])
        if a.audit_input:
            cmd.append('--no-strategy-review')
        if a.audit_only:
            cmd.append('--no-integrate')
        cmd.extend(['--task', 'Complete the selected quantum-code research obligation. '
                    'Preserve and explore proof routes, including local selector expansions. '
                    'A gap in an argument does not exclude its route. Prefer constructive progress '
                    'and precise repairs. Do not inherit historical route-exclusion claims as premises. '
                    'If audit seeds are supplied, finish fresh independent audits of those unchanged '
                    'compositions before creating any replacement proof.'])
        if a.live:cmd.append('--live')
    return subprocess.call(cmd,cwd=ROOT)
if __name__=='__main__':raise SystemExit(main())
