from pathlib import Path
import json,hashlib,shutil
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');src=repo/'pipelines/quantum_formalize/examples/m7/prefix_sector';b=repo/'pipelines/quantum_formalize/examples/m7/prefix_completed';p=Path('/home/jing/m7-lean-prefix-completed-formalization');p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True)
m=json.loads((src/'experiment/MANIFEST.json').read_text())
for n,h in m.items():assert hashlib.sha256((src/'experiment'/n).read_bytes()).hexdigest()==h,n
env=json.loads((src/'experiment/environment.json').read_text())
for f in (src/'lean').glob('*.lean'):
 assert hashlib.sha256(f.read_bytes()).hexdigest()==env[f.name],f.name
 shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name)
a=src/'experiment/AcceptedExperiment.lean';shutil.copy2(a,p/'M7PrefixSectorAccepted.lean');shutil.copy2(a,b/'lean/M7PrefixSectorAccepted.lean')
source='''import M7PrefixSectorAccepted

namespace M7.PrefixCompleted
def Base (N : ℕ) (A B WA WB : Finset ℕ) : Prop :=
  0 ∈ A ∧ 0 ∈ B ∧ A ⊆ Finset.range N ∧ B ⊆ Finset.range N ∧
  WA ⊆ Finset.range N ∧ WB ⊆ Finset.range N ∧ Disjoint A WA ∧ Disjoint B WB
def Within (A B WA WB : Finset ℕ) (x : Finset ℕ × Finset ℕ) : Prop :=
  A ⊆ x.1 ∧ x.1 ⊆ A ∪ WA ∧ B ⊆ x.2 ∧ x.2 ⊆ B ∪ WB
def Valid (N w : ℕ) (E : Finset M5.BinaryPolynomial) (x : Finset ℕ × Finset ℕ) : Prop :=
  x.1.card = w ∧ x.2.card = w ∧ M5.Connectivity.supportGcd N x.1 x.2 = 1 ∧
  M5.completeSignature (M5.SupportPolynomial.ofSupport x.1) (M5.SupportPolynomial.ofSupport x.2) N ∈ E
noncomputable def completed (N w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact (M7.PrefixSector.completions N w E A B WA WB).image (fun x => (A ∪ x.1, B ∪ x.2))
end M7.PrefixCompleted
'''
(p/'M7PrefixCompleted.lean').write_text(source);(b/'lean/M7PrefixCompleted.lean').write_text(source)
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text().replace('name = "M7PrefixSector"\nversion','name = "M7PrefixCompleted"\nversion').replace('defaultTargets = ["M7PrefixSector"]','defaultTargets = ["M7PrefixCompleted"]')+'\n[[lean_lib]]\nname = "M7PrefixSectorAccepted"\n\n[[lean_lib]]\nname = "M7PrefixCompleted"\n';(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
c='∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), ';d='Disjoint A WA → Disjoint B WB → ';base='M7.PrefixCompleted.Base N A B WA WB';count=lambda A='A',B='B',WA='WA',WB='WB':f'M7.PrefixSector.count N w E {A} {B} {WA} {WB}';comp=lambda A='A',B='B',WA='WA',WB='WB':f'M7.PrefixCompleted.completed N w E {A} {B} {WA} {WB}'
items=[
('union_injective',[],c+d+'Set.InjOn (fun x : Finset ℕ × Finset ℕ => (A ∪ x.1, B ∪ x.2)) (M7.PrefixSector.completions N w E A B WA WB : Set (Finset ℕ × Finset ℕ))'),
('completed_membership',[],c+d+'∀ x, x ∈ '+comp()+' ↔ M7.PrefixCompleted.Within A B WA WB x ∧ M7.PrefixCompleted.Valid N w E x'),
('overfull_empty',[],c+'(w < A.card ∨ w < B.card) → '+comp()+' = ∅'),
('count_completed',['union_injective','overfull_empty'],c+'0 < N → M7.PrefixSector.ValidSector N E → '+base+' → '+count()+' = ('+comp()+').card'),
('left_children',[],c+'∀ i ∈ WA, '+base+' → M7.PrefixCompleted.Base N A B (WA.erase i) WB ∧ M7.PrefixCompleted.Base N (insert i A) B (WA.erase i) WB'),
('right_children',[],c+'∀ i ∈ WB, '+base+' → M7.PrefixCompleted.Base N A B WA (WB.erase i) ∧ M7.PrefixCompleted.Base N A (insert i B) WA (WB.erase i)'),
('left_sets',['completed_membership'],c+d+'∀ i ∈ WA, '+comp()+' = '+comp(WA='(WA.erase i)')+' ∪ '+comp(A='(insert i A)',WA='(WA.erase i)')),
('right_sets',['completed_membership'],c+d+'∀ i ∈ WB, '+comp()+' = '+comp(WB='(WB.erase i)')+' ∪ '+comp(B='(insert i B)',WB='(WB.erase i)')),
('left_disjoint',['completed_membership'],c+d+'∀ i ∈ WA, Disjoint ('+comp(WA='(WA.erase i)')+') ('+comp(A='(insert i A)',WA='(WA.erase i)')+')'),
('right_disjoint',['completed_membership'],c+d+'∀ i ∈ WB, Disjoint ('+comp(WB='(WB.erase i)')+') ('+comp(B='(insert i B)',WB='(WB.erase i)')+')'),
('left_count_split',['count_completed','left_children','left_sets','left_disjoint'],c+'0 < N → M7.PrefixSector.ValidSector N E → '+base+' → ∀ i ∈ WA, '+count()+' = '+count(WA='(WA.erase i)')+' + '+count(A='(insert i A)',WA='(WA.erase i)')),
('right_count_split',['count_completed','right_children','right_sets','right_disjoint'],c+'0 < N → M7.PrefixSector.ValidSector N E → '+base+' → ∀ i ∈ WB, '+count()+' = '+count(WB='(WB.erase i)')+' + '+count(B='(insert i B)',WB='(WB.erase i)'))]
g={'title':'M7 actual arithmetic prefix counts on literal completed supports and binary child partitions','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M7.PrefixCompleted.'+i,'statement':s,'imports':['M7PrefixCompleted'],'context':'','queries':['algebra'],'guidance':'Preserve actual arithmetic count definition. completed is proof-only image of residual completions, not generation implementation. Use accepted PrefixSector count identity and overfull_zero. Disjoint selected/undecided supports make union injective; inverse residual is x.1 \\ A and x.2 \\ B. For membership use Finset powersetCard/subset/card_sdiff and actual validCompletions filter. Base deliberately has no card<=w: count_completed handles overfull branches by zero. Child sets split by membership of i, and selected/undecided disjointness yields disjoint physical outputs. Return tactic lines only.\n'+source}}for i,deps,s in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7PrefixCompleted\n'+''.join('def target_'+str(j)+' : Prop := '+s+'\n'for j,(_,_,s)in enumerate(items)))
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'parent':'../prefix_sector','canonical_experiment_files_verified':len(m),'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'copied_source_hashes':{f.name:hashlib.sha256(f.read_bytes()).hexdigest()for f in (b/'lean').glob('*.lean')if f.name!='M7PrefixCompleted.lean'}},indent=2)+'\n')
(b/'SCOPE.md').write_text('# Literal completed supports and actual arithmetic child partitions\n\nTwelve exact targets connect the actual M5 sector arithmetic to physical completed support pairs and prove both binary child partitions, including overfull selected children. completed is a semantic proof specification; the count and later generator remain arithmetic. Cyclic residue conversion and residual orbit subtraction are separate downstream gates.\n');print('prepared12 exact targets with verified prefix_sector9 import')
