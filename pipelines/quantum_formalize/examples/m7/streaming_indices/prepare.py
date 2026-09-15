from pathlib import Path
import json,hashlib,shutil,subprocess,os
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');base=repo/'pipelines/quantum_formalize/examples/m7';src=base/'global_query';b=base/'streaming_indices';p=Path('/home/jing/m7-lean-streaming-indices-formalization')
b.mkdir(exist_ok=True);(b/'lean').mkdir(exist_ok=True);p.mkdir(exist_ok=True)
r=json.loads((src/'experiment/result.json').read_text());assert all(r[k] for k in ['assembly_accepted','environment_unchanged','experiment_passed'])
manifest=json.loads((src/'experiment/MANIFEST.json').read_text());m=manifest.get('files',manifest);env=json.loads((src/'experiment/environment.json').read_text())
for f,h in m.items():assert hashlib.sha256((src/'experiment'/f).read_bytes()).hexdigest()==h,f
files=[]
for f in (src/'lean').glob('*.lean'):
 if f.name not in env:continue
 h=hashlib.sha256(f.read_bytes()).hexdigest();assert env[f.name]==h,f
 shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name);files.append({'file':f.name,'sha256':h})
a=src/'experiment/AcceptedExperiment.lean';shutil.copy2(a,p/'M7GlobalQueryAccepted.lean');shutil.copy2(a,b/'lean/M7GlobalQueryAccepted.lean')
source='''import M7GlobalQueryAccepted

namespace M7.StreamingIndices
/-- Bounded tail recursion; no list or full index collection is constructed. -/
def allFinFrom (n : ℕ) (p : Fin n → Bool) (i : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 => if hi : i < n then
      if p ⟨i, hi⟩ then allFinFrom n p (i + 1) fuel else false
    else true

def allFin (n : ℕ) (p : Fin n → Bool) : Bool := allFinFrom n p 0 n

noncomputable def decodeRecord (N : ℕ) [NeZero N]
    (u : Fin (Fintype.card ((ZMod N)ˣ))) (e : Fin 2) (s t : Fin N) : M7.Action.Record N :=
  { unit := (Fintype.equivFin ((ZMod N)ˣ)).symm u
    exchange := decide (e.val = 1)
    leftShift := (s.val : ZMod N)
    rightShift := (t.val : ZMod N) }

noncomputable def allRecords (N : ℕ) [NeZero N] (p : M7.Action.Record N → Bool) : Bool :=
  allFin (Fintype.card ((ZMod N)ˣ)) (fun u =>
    allFin 2 (fun e => allFin N (fun s => allFin N (fun t => p (decodeRecord N u e s t)))))

noncomputable def allIndices (H N : ℕ) [NeZero N] (p : M7.GlobalQuery.Index H N → Bool) : Bool :=
  allFin H (fun h => allRecords N (fun g => p (h, g)))

noncomputable def streamWin {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N) : Bool := by
  classical
  exact decide (M7.GlobalQuery.feasible q bases x) &&
    allIndices H N (fun y => decide (M7.GlobalQuery.feasible q bases y →
      ¬ M7.Selection.better q.order (M7.GlobalQuery.objective q bases y)
        (M7.GlobalQuery.objective q bases x)))
end M7.StreamingIndices
'''
(p/'M7StreamingIndices.lean').write_text(source);(b/'lean/M7StreamingIndices.lean').write_text(source)
ns='M7.StreamingIndices.'
items=[
('cursor_interval',[], '∀ (n : ℕ) (p : Fin n → Bool) (i fuel : ℕ), '+ns+'allFinFrom n p i fuel = true ↔ ∀ j : Fin n, i ≤ j.val → j.val < i + fuel → p j = true'),
('all_fin',['cursor_interval'],'∀ (n : ℕ) (p : Fin n → Bool), '+ns+'allFin n p = true ↔ ∀ j : Fin n, p j = true'),
('record_surjective',[], '∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, ∃ (u : Fin (Fintype.card ((ZMod N)ˣ))) (e : Fin 2) (s t : Fin N), '+ns+'decodeRecord N u e s t = g'),
('all_records',['all_fin','record_surjective'],'∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → Bool, '+ns+'allRecords N p = true ↔ ∀ g : M7.Action.Record N, p g = true'),
('all_indices',['all_fin','all_records'],'∀ (H N : ℕ) [NeZero N], ∀ p : M7.GlobalQuery.Index H N → Bool, '+ns+'allIndices H N p = true ↔ ∀ x : M7.GlobalQuery.Index H N, p x = true'),
('stream_winners',['all_indices'],'∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), '+ns+'streamWin q bases x = true ↔ x ∈ M7.GlobalQuery.winners q bases')]
guide='''Original M7 §11 streaming action-index comparison implementation. allFinFrom is actual tail recursion over a decreasing Nat fuel, no List.range/Finset.univ.toList or global index ledger. Prove cursor_interval by induction fuel generalizing i, split i<n and p(current), use omega on the interval and Fin.ext for equal values. all_fin specializes i=0 fuel=n. record_surjective: encode g.unit using Fintype.equivFin, Bool cases give e=0 or 1, use Fin indices ⟨g.leftShift.val,ZMod.val_lt _⟩ and right, natCast_zmod_val. Do not assume N>1: both exchange flags exist at N=1. all_records repeatedly applies all_fin and uses actual record_surjective. all_indices uses all_fin/all_records and Prod.forall. stream_winners unfolds actual streamWin, Boolean and/decide and all_indices then applies (M7.GlobalQuery.winners_exact H N q bases).1 x in reverse. No arbitrary feasibility/objective oracle appears in streamWin. No new cost hypothesis, efficiency requirement, label oracle or target weakening. Return tactic lines only; no leading by.\n'''+source
g={'title':'M7 actual streaming action-index cursors and exact winners','nodes':[{'id':i,'dependencies':d,'spec':{'name':ns+i,'statement':s,'imports':['M7StreamingIndices'],'context':'','queries':['algebra'],'guidance':guide}}for i,d,s in items]}
(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');pre='import M7StreamingIndices\n'+''.join('def target_'+str(j)+' : Prop := ('+s+')\n'for j,(_,_,s)in enumerate(items));(p/'Preflight.lean').write_text(pre);(b/'GraphPreflight.lean').write_text(pre)
for n in ['lean-toolchain','lake-manifest.json']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
lake='''name = "M7StreamingIndices"
version = "0.1.0"
defaultTargets = ["M7StreamingIndices"]
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
'''
for f in sorted(p.glob('*.lean')):
 if f.stem!='Preflight':lake+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(lake);(b/'lakefile.toml').write_text(lake);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'parent':'global_query','canonical_files_verified':len(m),'all_parent_gates':True,'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'sources':files},indent=2)+'\n')
(b/'SCOPE.md').write_text('Original M7 §11: actual bounded Nat cursors traverse H/unit/exchange/two shifts and implement the exact actual winner predicate without constructing a full action-index list. The unit equivalence is finite preprocessing. Semantic winners remain only the theorem RHS. This batch proves traversal and winner correctness; it does not claim an operation bound for arbitrary label evaluation or full M7 completion.\n')
ctl=Path('/home/jing/m7_canonical_preflight_launch.py').read_text().replace('canonical-block','streaming-indices').replace('canonical_block','streaming_indices').replace('M7CanonicalBlock','M7StreamingIndices').replace('13 exact','6 exact').replace("env['M7_COMPILE_TIMEOUT']='600'","env['M7_COMPILE_TIMEOUT']='600';env['M7_BROAD_RETRIEVAL']='1'")
c=Path('/home/jing/m7_streaming_indices_preflight_launch.py');c.write_text(ctl);(b/'preflight_launch.py').write_text(ctl);shutil.copy2('/home/jing/m7_launch_batch.py',b/'launch_batch.py')
log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(c)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print({'targets':6,'controller_pid':proc.pid})
