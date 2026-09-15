from pathlib import Path
import json,tempfile
from pipelines.quantum_formalize.engine import Spec,verify,save,fingerprint
p=Path('/home/jing/m7-lean-final-replay-formalization');old=p/'.humanize-formal-runs/run-b71j2k_u'
a=Path(tempfile.mkdtemp(prefix='presentation-bool-repair-',dir=p/'.humanize-formal-runs'))
s=Spec.model_validate(json.loads((old/'spec.json').read_text()))
proof='''unfold QuantumHarnessFrozenTarget
classical
intro N w inst q hw hwN c hc y
have hv := ((M7.FinalReplay.parts N w q c).mp hc).1
have hsets := (M7.FinalReplay.checked_sets N w q hw hwN c hc).2
rw [hsets]
have h := M7.FinalSelector.presentation_exact N w q hw hwN hv y
have hp : ∀ x : M7.FinalSelector.Index N w q,
    M7.FinalSelector.present q x = true ↔
      M7.GlobalQuery.present q (M7.FinalSelector.family N w q) x := by
  intro x
  unfold M7.FinalSelector.present
  rw [Bool.and_eq_true, decide_eq_true_eq]
  rw [M7.FinalSelector.win, M7.StreamingIndices.stream_winners]
  rfl
simpa only [hp, M7.QueryCertificate.allPresentations,
  Finset.mem_filter, Finset.mem_univ, true_and] using h'''
save(a/'draft.json',{'proof':proof,'queries':[]});save(a/'spec.json',s.model_dump());before=fingerprint(p);r=verify(s,proof,p,a,timeout=600);r['environment_unchanged']=before==fingerprint(p);save(a/'verdict.json',r);save(Path('/home/jing/m7-replay-presentation-repair.json'),{'directory':str(a),'verdict':r,'origin':'Exact local repair after five live failures: explicitly rewrite the Boolean/decide predicate to the accepted GlobalQuery presentation predicate and finite-set membership. Original target and frozen definitions unchanged.'});print(json.dumps(r))
