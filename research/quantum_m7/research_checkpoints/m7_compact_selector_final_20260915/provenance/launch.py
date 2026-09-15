from pathlib import Path
import json, subprocess
repo=Path('/home/jing/quantum_code_discovery_proof')
harness=Path('/home/jing/science-mango-m7-scope-20260915')
area=repo/'.humanize-quantum-runs/m7-final-scope-20260915'
seed=area/'audit-seed.json'
assert seed.is_file(), 'Prepare and inspect the final seed before launching'
cmd=[str(repo/'.venv-harness/bin/python'),'-u','-m','pipelines.quantum_humanize','launch','--repo',str(repo),'--obligation','selector','--model','gpt-6-astra','--effort','medium','--parallelism','2','--attempts','1','--rounds','1','--max-calls','32','--no-integrate','--no-strategy-review','--no-coverage-planning','--turn-timeout-seconds','3600','--audit-continuations','4','--audit-input',str(seed.relative_to(repo))]
for folder in ['docs','scripts','tests','evidence','data']:
    for f in sorted((repo/folder).iterdir()):
        if f.is_file() and f.suffix in {'.md','.py','.json','.jsonl','.csv'}:
            cmd.extend(['--extra-input',str(f.relative_to(repo))])
task='Perform fresh independent dual review of the exact final M7 audit seed and its entire dependency closure. Read docs/M7_FINAL_SCOPE_AUDIT_20260915.md for current assignment and implementation boundary. Assess the original gate against the actual mathematical constructions, including compact generation, exact distance and witness interfaces, all certified optimal classes and tied physical placements, empty answers and replay. Do not presume correctness or completion; identify any real gap precisely. Current M5 arithmetic and M6 exact-reduction proofs must be checked, while their historical open-status prose and M8 efficiency are not additional gates. No historical review votes are imported. This is an unchanged artifact audit, not a request to discover a new theorem.'
cmd.extend(['--task',task,'--live'])
(area/'launch-argv.json').write_text(json.dumps(cmd,indent=2)+'\n')
print('Final current-scope M7 audit log: '+str(area/'launch.log'),flush=True)
with (area/'launch.log').open('a') as log:
    result=subprocess.run(cmd,cwd=harness,stdout=log,stderr=subprocess.STDOUT)
(area/'exit.json').write_text(json.dumps({'exit_code':result.returncode})+'\n')
raise SystemExit(result.returncode)
