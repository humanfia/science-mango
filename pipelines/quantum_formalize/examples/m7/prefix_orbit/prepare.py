from pathlib import Path
import json,hashlib,shutil,subprocess,re,time
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');base=repo/'pipelines/quantum_formalize/examples/m7';b=base/'prefix_orbit';p=Path('/home/jing/m7-lean-prefix-orbit-formalization');parents=[('residue_prefix','M7ResiduePrefixAccepted'),('actual_signature','M7RecipeSignatureAccepted'),('connectivity','M7ConnectivityAccepted'),('canonical_classes','M7CanonicalClassesAccepted'),('orbit_residual','M7OrbitResidualAccepted')]
# This preparer is launched only after the controller has checked every canonical gate.
p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True);prov=[]
for name,accepted in parents:
 src=base/name;r=json.loads((src/'experiment/result.json').read_text());assert all(r.get(k)is True for k in ['assembly_accepted','environment_unchanged','experiment_passed']),name
 m=json.loads((src/'experiment/MANIFEST.json').read_text());env=json.loads((src/'experiment/environment.json').read_text())
 for n,h in m.items():assert hashlib.sha256((src/'experiment'/n).read_bytes()).hexdigest()==h,(name,n)
 for f in (src/'lean').glob('*.lean'):
  if f.name not in env:continue
  assert hashlib.sha256(f.read_bytes()).hexdigest()==env[f.name],(name,f.name)
  if(p/f.name).exists():assert(p/f.name).read_bytes()==f.read_bytes(),('source collision',name,f.name)
  shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name)
 a=src/'experiment/AcceptedExperiment.lean'
 if(p/(accepted+'.lean')).exists():assert(p/(accepted+'.lean')).read_bytes()==a.read_bytes(),('accepted collision',accepted)
 shutil.copy2(a,p/(accepted+'.lean'));shutil.copy2(a,b/'lean'/(accepted+'.lean'));prov.append({'parent':name,'canonical_files_verified':len(m),'all_sources_match_environment':True,'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest()})
source='''import M7ResiduePrefixAccepted
import M7RecipeSignatureAccepted
import M7ConnectivityAccepted
import M7CanonicalClassesAccepted
import M7OrbitResidualAccepted

namespace M7.PrefixOrbit
open scoped BigOperators
def Within {N : ℕ} (D W : Finset ℕ) (S : Finset (ZMod N)) : Prop :=
  D ⊆ M7.ResiduePrefix.encode S ∧ M7.ResiduePrefix.encode S ⊆ D ∪ W
def ClassValid {N : ℕ} (w : ℕ) (c : M7.Action.Recipe N) : Prop :=
  c.1.card = w ∧ c.2.card = w ∧ M7.Connectivity.connected c
noncomputable def orbitCount {N : ℕ} [NeZero N] (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) (c : M7.Action.Recipe N) : ℕ :=
  M7.RecipeSignature.sourceCount c (fun F => F ∈ E) (Within A WA) (Within B WB)
noncomputable def residual {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) (bases : Finset (M7.Action.Recipe N)) : ℤ :=
  M7.PrefixSector.count N w E A B WA WB - ∑ c ∈ bases, (orbitCount E A B WA WB c : ℤ)
end M7.PrefixOrbit
'''
(p/'M7PrefixOrbit.lean').write_text(source);(b/'lean/M7PrefixOrbit.lean').write_text(source)
src=base/'residue_prefix'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M7PrefixOrbit"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M7PrefixOrbit"]',s,flags=re.M)
for f in sorted(p.glob('*.lean')):
 if f.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N], ';r='M7.Action.Recipe N';po='M7.PrefixOrbit.';within=po+'Within';cv=po+'ClassValid w ';basep='M7.PrefixCompleted.Base N A B WA WB';cc='M7.ResiduePrefix.completed N w E A B WA WB';args='∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), ';validE='M7.PrefixSector.ValidSector N E';norm='M7.CanonicalClasses.Normalized bases';res=po+'residual w E A B WA WB bases'
items=[
('prefix_anchors',[],f+'∀ (A B WA WB : Finset ℕ) (y : '+r+'), '+basep+' → '+within+' A WA y.1 → '+within+' B WB y.2 → (0 : ZMod N) ∈ y.1 ∧ (0 : ZMod N) ∈ y.2'),
('gcd_bridge',[],f+'∀ y : '+r+', M7.Domain.connectivityGcd y.1 y.2 = M5.Connectivity.supportGcd N (M7.ResiduePrefix.encode y.1) (M7.ResiduePrefix.encode y.2)'),
('membership',['prefix_anchors','gcd_bridge'],f+args+basep+' → ∀ y : '+r+', y ∈ '+cc+' ↔ '+cv+'y ∧ M7.RecipeSignature.signature y ∈ E ∧ '+within+' A WA y.1 ∧ '+within+' B WB y.2'),
('class_action',[],f+'∀ (w : ℕ) (c : '+r+') (g : M7.Action.Record N), '+cv+'c → '+cv+'(M7.Action.act g c)'),
('source_count',['membership','class_action'],f+args+basep+' → ∀ c : '+r+', '+cv+'c → '+po+'orbitCount E A B WA WB c = M7.ActualOrbit.distinctCount c (fun y => y ∈ '+cc+')'),
('residual_eq',['source_count'],f+args+validE+' → '+basep+' → ∀ bases : Finset ('+r+'), (∀ c ∈ bases, '+cv+'c) → '+res+' = M7.OrbitResidual.subtraction ('+cc+') bases'),
('residual_card',['residual_eq'],f+args+validE+' → '+basep+' → ∀ bases : Finset ('+r+'), (∀ c ∈ bases, '+cv+'c) → '+norm+' → '+res+' = (M7.OrbitResidual.remaining ('+cc+') bases).card'),
('residual_positive',['residual_eq'],f+args+validE+' → '+basep+' → ∀ bases : Finset ('+r+'), (∀ c ∈ bases, '+cv+'c) → '+norm+' → 0 ≤ '+res+' ∧ (0 < '+res+' ↔ ∃ y ∈ '+cc+', y ∉ M7.OrbitResidual.covered bases)'),
('emitted_class_valid',['membership','class_action'],f+args+basep+' → ∀ y ∈ '+cc+', '+cv+'(M7.CanonicalOuter.canonical y)')]
guide='''This instantiates original M7 arithmetic orbit-prefix subtraction with concrete supports and exact original counts. No free TranslationInvariant, complete transversal or count oracle remains in these target interfaces. Prefix anchors come from Base's selected zero and Within/encode; residue_roundtrip converts membership. gcd_bridge is the accepted ResiduePrefix.gcd_union with Domain's literal gcd union. Membership uses ResiduePrefix.completed_membership, encode_card, signature_bridge and Connectivity.anchored_gcd after prefix_anchors. ClassValid is equal weight plus the unique actual subgroup-connected predicate; preserve it with Action.support_cards and Connectivity.connected_action. source_count uses accepted RecipeSignature.source_orbit_quotient. On each actual orbit image, ClassValid follows by class_action, so the actual source sector/left/right predicate equals completed-set membership. Use Finset.filter_congr for predicate equality; align classical DecidablePred explicitly or Finset.filter_congr_decidable if needed. residual_eq uses accepted ResiduePrefix.count_completed and source_count termwise. Normalized stored values discharge Separated via CanonicalClasses.normalized_separated, giving remaining-cardinality/nonnegative-positive through the accepted OrbitResidual identities. A canonical emitted signature need not belong to E: only ClassValid is preserved by the actual realizer. All full multiplicities, even N, N=1 and empty E stay included. Return tactic lines only.\n'''+source
g={'title':'M7 actual arithmetic orbit-prefix and residual invariant integration','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M7.PrefixOrbit.'+i,'statement':st,'imports':['M7PrefixOrbit'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7PrefixOrbit\n'+''.join('def target_'+str(j)+' : Prop := '+st+'\n'for j,(_,_,st)in enumerate(items)));(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(b/'SCOPE.md').write_text('# Concrete arithmetic residual integration\n\nNine targets identify the original factorized source orbit quotient with the actual prefix completion subset, then identify actual arithmetic subtraction with the remaining-set cardinality. Actual class validity and normalized stored values discharge connectedness, weight and separation. No complete transversal/count/automorphism/distance oracle is introduced. Compact binary recovery, iteration, raw coverage and final replay still require downstream closure.\n')
ctl=Path('/home/jing/m7_canonical_preflight_launch.py').read_text().replace('canonical-block','prefix-orbit').replace('canonical_block','prefix_orbit').replace('M7CanonicalBlock','M7PrefixOrbit').replace('13 exact','9 exact').replace("env['M7_COMPILE_TIMEOUT']='600'","env['M7_COMPILE_TIMEOUT']='600';env['M7_BROAD_RETRIEVAL']='1'");cp=Path('/home/jing/m7_prefix_orbit_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m7_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'prepared':9,'controller_pid':proc.pid})
