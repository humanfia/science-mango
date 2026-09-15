from pathlib import Path
import json,tempfile
from pipelines.quantum_formalize.engine import Spec,verify,save,fingerprint
p=Path('/home/jing/m7-lean-final-resources-formalization');old=p/'.humanize-formal-runs/run-z7pd0u95'
a=Path(tempfile.mkdtemp(prefix='generation-card-repair-',dir=p/'.humanize-formal-runs'))
s=Spec.model_validate(json.loads((old/'spec.json').read_text()))
proof='''intro N w inst E hw hwN hE
dsimp only [M7.GeneratedFamily.size]
have hc := M7.CompactCorrectness.generate_card N w E hE
obtain ⟨_, hcount, horbits⟩ := M7.GenerationCalls.generate_count N w E
refine ⟨hc, hcount, ?_⟩
simpa only [hc] using horbits'''
save(a/'draft.json',{'proof':proof,'queries':[]});save(a/'spec.json',s.model_dump());before=fingerprint(p);r=verify(s,proof,p,a,timeout=600);r['environment_unchanged']=before==fingerprint(p);save(a/'verdict.json',r);save(Path('/home/jing/m7-resources-generation-repair.json'),{'directory':str(a),'verdict':r,'origin':'Exact local repair after five live failures: unfold family size, use canonical generate_card with its actual argument list and rewrite the existing orbit bound. Original target and frozen definitions unchanged.'});print(json.dumps(r))
