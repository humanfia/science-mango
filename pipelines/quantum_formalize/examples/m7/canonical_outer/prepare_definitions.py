from pathlib import Path
import json,hashlib,shutil
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');root=repo/'pipelines/quantum_formalize/examples/m7';b=root/'canonical_outer';p=Path('/home/jing/m7-lean-canonical-outer-formalization');p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True);verified={}
for module,names in [('group',['M7Action','M7ActionAccepted','M7ActionGroup']),('canonical_block',['M7CanonicalBlock'])]:
 src=root/module;env=json.loads((src/'experiment/environment.json').read_text());manifest=json.loads((src/'experiment/MANIFEST.json').read_text())
 for n,h in manifest.items():assert hashlib.sha256((src/'experiment'/n).read_bytes()).hexdigest()==h,n
 for name in names:
  f=src/'lean'/(name+'.lean');h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==env[f.name],name;verified[module+'/'+f.name]=h;shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name)
a=root/'canonical_block/experiment/AcceptedExperiment.lean';shutil.copy2(a,p/'M7CanonicalBlockAccepted.lean');shutil.copy2(a,b/'lean/M7CanonicalBlockAccepted.lean');verified['canonical_block/AcceptedExperiment.lean']=hashlib.sha256(a.read_bytes()).hexdigest()
source='''import M7ActionGroup
import M7CanonicalBlockAccepted

namespace M7.CanonicalOuter
abbrev OuterIndex (N : ℕ) := Lex (Fin N × Bool)
abbrev PairKey := Lex (List ℕ × List ℕ)
abbrev ChoiceKey (N : ℕ) := Lex (PairKey × OuterIndex N)
noncomputable def indices (N : ℕ) [NeZero N] : Finset (OuterIndex N) := by
  classical
  exact Finset.univ.filter (fun i => IsUnit (((ofLex i).1.val : ℕ) : ZMod N))
noncomputable def outerUnit {N : ℕ} [NeZero N] (i : OuterIndex N) : (ZMod N)ˣ := by
  classical
  exact if h : IsUnit (((ofLex i).1.val : ℕ) : ZMod N) then h.unit else 1
noncomputable def outerRecord {N : ℕ} [NeZero N] (i : OuterIndex N) : M7.Action.Record N :=
  ⟨outerUnit i, (ofLex i).2, 0, 0⟩
noncomputable def normalizePair {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : M7.Action.Recipe N :=
  (M7.CanonicalBlock.normalize c.1, M7.CanonicalBlock.normalize c.2)
noncomputable def pairKey {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : PairKey :=
  toLex (M7.CanonicalBlock.key c.1, M7.CanonicalBlock.key c.2)
noncomputable def candidate {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (i : OuterIndex N) : M7.Action.Recipe N :=
  normalizePair (M7.Action.act (outerRecord i) c)
noncomputable def choices {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Finset (ChoiceKey N) :=
  (indices N).image (fun i => toLex (pairKey (candidate c i), i))
noncomputable def best {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : ChoiceKey N :=
  if h : (choices c).Nonempty then (choices c).min' h
  else toLex (toLex ([], []), toLex (⟨0, NeZero.pos N⟩, false))
noncomputable def chosenOuter {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : OuterIndex N :=
  (ofLex (best c)).2
noncomputable def canonical {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : M7.Action.Recipe N :=
  candidate c (chosenOuter c)
noncomputable def realizer {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : M7.Action.Record N :=
  let g := outerRecord (chosenOuter c)
  let r := M7.Action.act g c
  M7.Action.compose (M7.Action.translate (-M7.CanonicalBlock.bestAnchor r.1) (-M7.CanonicalBlock.bestAnchor r.2)) g
noncomputable def keyset {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Finset PairKey :=
  (indices N).image (fun i => pairKey (candidate c i))
end M7.CanonicalOuter
'''
(p/'M7CanonicalOuter.lean').write_text(source);(b/'lean/M7CanonicalOuter.lean').write_text(source)
base=root/'canonical_block'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(base/n,p/n);shutil.copy2(base/n,b/n)
s=(base/'lakefile.toml').read_text().replace('M7CanonicalBlock','M7CanonicalOuter')+''.join('\n[[lean_lib]]\nname = '+json.dumps(f.stem)+'\n'for f in sorted(p.glob('*.lean'))if f.stem!='M7CanonicalOuter');(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'canonical_source_and_environment_hashes_verified':True,'copied_imports':verified},indent=2)+'\n')
print('Prepared explicit outer-unit/exchange normalization definitions with retained actual action')
