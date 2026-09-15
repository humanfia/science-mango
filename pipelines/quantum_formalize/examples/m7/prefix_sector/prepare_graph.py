from pathlib import Path
import json,hashlib,shutil,re
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');src=repo/'pipelines/quantum_formalize/examples/m5/stage48';b=repo/'pipelines/quantum_formalize/examples/m7/prefix_sector';p=Path('/home/jing/m7-lean-prefix-sector-formalization')
p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True)
manifest=json.loads((src/'MANIFEST.json').read_text())['files'];seen={}
def copy(name):
 if name in seen:return
 f=src/'lean'/(name+'.lean');data=f.read_bytes();h=hashlib.sha256(data).hexdigest();assert h==manifest['lean/'+f.name],name;seen[name]=h
 for line in data.decode().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():
    if dep.startswith('M5'):copy(dep)
 shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name)
copy('M5ConditionalCountAccepted')
text='''import M5ConditionalCountAccepted

namespace M7.PrefixSector
noncomputable def count (N w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : ℤ :=
  ∑ F ∈ E, M5.ConditionalCount.completionC N w F A B WA WB
noncomputable def completions (N w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact E.biUnion (fun F => M5.ConditionalCount.validCompletions N w F A B WA WB)
def ValidSector (N : ℕ) (E : Finset M5.BinaryPolynomial) : Prop :=
  ∀ F ∈ E, F.Monic ∧ F ∣ M5.cyclicModulus N
end M7.PrefixSector
'''
(p/'M7PrefixSector.lean').write_text(text);(b/'lean/M7PrefixSector.lean').write_text(text)
base=Path('/home/jing/m7-lean-canonical-block-formalization')
for name in ['lake-manifest.json','lean-toolchain']:shutil.copy2(base/name,p/name);shutil.copy2(base/name,b/name)
(p/'lakefile.toml').write_text((base/'lakefile.toml').read_text().replace('M7CanonicalBlock','M7PrefixSector') + ''.join('\n[[lean_lib]]\nname = '+json.dumps(name)+'\n' for name in sorted(seen)));shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not (p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'source':'../m5/stage48','verified_against_canonical_manifest':True,'byte_identical_local_imports':seen,'module_count':len(seen)},indent=2)+'\n')
common='∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), '
h='0 < N → M7.PrefixSector.ValidSector N E → M5.ConditionalCount.PrefixOK N w A B WA WB → '
c='M7.PrefixSector.count N w E A B WA WB';v='M7.PrefixSector.completions N w E A B WA WB'
items=[
('disjoint_signatures',[],'∀ (N w : ℕ) (F G : M5.BinaryPolynomial) (A B WA WB : Finset ℕ), F ≠ G → Disjoint (M5.ConditionalCount.validCompletions N w F A B WA WB) (M5.ConditionalCount.validCompletions N w G A B WA WB)'),
('completion_membership',[],common+'∀ x, x ∈ '+v+' ↔ ∃ F ∈ E, x ∈ M5.ConditionalCount.validCompletions N w F A B WA WB'),
('exact_sector_count',['disjoint_signatures'],common+h+c+' = ('+v+').card'),
('count_nonnegative',[],common+h+'0 ≤ '+c),
('positive_iff',['exact_sector_count'],common+h+'(0 < '+c+' ↔ ('+v+').Nonempty)'),
('empty_sector',[],'∀ (N w : ℕ) (A B WA WB : Finset ℕ), M7.PrefixSector.count N w ∅ A B WA WB = 0 ∧ M7.PrefixSector.completions N w ∅ A B WA WB = ∅'),
('disjoint_sector_sum',[],'∀ (N w : ℕ) (E H : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint E H → M7.PrefixSector.count N w (E ∪ H) A B WA WB = M7.PrefixSector.count N w E A B WA WB + M7.PrefixSector.count N w H A B WA WB'),
('overfull_zero',[],common+'(w < A.card ∨ w < B.card) → '+c+' = 0'),
('leaf_zero_one',['exact_sector_count'],'∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M5.ConditionalCount.PrefixOK N w A B ∅ ∅ → M7.PrefixSector.count N w E A B ∅ ∅ = (if A.card = w ∧ B.card = w ∧ M5.Connectivity.supportGcd N A B = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N ∈ E then (1 : ℤ) else 0)')]
g={'title':'M7 actual M5 arithmetic prefix counts across finite full-signature sectors','nodes':[{'id':i,'dependencies':d,'spec':{'name':'M7.PrefixSector.'+i,'statement':s,'imports':['M7PrefixSector'],'context':'','queries':['addition commutativity'],'guidance':'Use accepted M5.ConditionalCount.exact_completion_C and completion_nonnegative_and_exists, not assumed count identities. Definitions and actual finite arithmetic are frozen. Distinct signatures make validCompletions disjoint. For leaf, WA=WB=empty means only possible residual pair is (empty,empty); no raw pair enumeration is introduced in count. Return tactic lines only.\n'+text}}for i,d,s in items]}
(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7PrefixSector\n'+''.join('def target_'+str(j)+' : Prop := '+s+'\n'for j,(_,_,s)in enumerate(items)))
(b/'SCOPE.md').write_text('# Actual sector prefix counts\n\nNine targets reuse actual M5 arithmetic completionC across a finite set of full signatures. Semantic completion sets are specifications only; count is the arithmetic sum. This is an intermediate component: child partitions, natural-exponent to ZMod support equivalence and actual residual generation remain downstream. No full M7 acceptance is claimed.\n')
print('Prepared',len(items),'targets; verified',len(seen),'M5 source modules')
