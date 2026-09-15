from pathlib import Path
import json,hashlib,shutil,subprocess
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');base=repo/'pipelines/quantum_formalize/examples/m7';b=base/'generation_replay';p=Path('/home/jing/m7-lean-generation-replay-formalization');parents=[('compact_correctness','M7CompactCorrectnessAccepted'),('raw_coverage','M7RawCoverageAccepted')]
b.mkdir(exist_ok=True);(b/'lean').mkdir(exist_ok=True);p.mkdir(exist_ok=True);provenance=[]
for name,accepted in parents:
 src=base/name;r=json.loads((src/'experiment/result.json').read_text());assert all(r[k] for k in ['assembly_accepted','environment_unchanged','experiment_passed'])
 manifest=json.loads((src/'experiment/MANIFEST.json').read_text());m=manifest.get('files',manifest);env=json.loads((src/'experiment/environment.json').read_text())
 for f,h in m.items():assert hashlib.sha256((src/'experiment'/f).read_bytes()).hexdigest()==h,(name,f)
 files=[]
 for f in (src/'lean').glob('*.lean'):
  if f.name not in env:continue
  h=hashlib.sha256(f.read_bytes()).hexdigest();assert env[f.name]==h,(name,f)
  if(p/f.name).exists():assert(p/f.name).read_bytes()==f.read_bytes(),('collision',f.name)
  shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name);files.append({'file':f.name,'sha256':h})
 a=src/'experiment/AcceptedExperiment.lean';shutil.copy2(a,p/(accepted+'.lean'));shutil.copy2(a,b/'lean'/(accepted+'.lean'))
 provenance.append({'parent':name,'canonical_files_verified':len(m),'all_parent_gates':True,'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'sources':files})
source='''import M7CompactCorrectnessAccepted
import M7RawCoverageAccepted

namespace M7.GenerationReplay
noncomputable section
open Classical

/-- Every stored field is recomputed from the actual current prefix count. -/
def stepPass {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (bases : Finset (M7.Action.Recipe N)) (e : M7.CompactGeneration.Emission N) : Bool :=
  decide (0 < M7.CompactGeneration.residual w E bases []) &&
    (M7.DescentTrace.check (M7.CompactGeneration.residual w E bases) [] e.path).1 &&
    decide (e.path.length = M7.PrefixBits.depth N ∧
      e.leaf = M7.ResiduePrefix.decodePair N
        (M7.PrefixBits.A N (M7.DescentTrace.endpoint [] e.path),
         M7.PrefixBits.B N (M7.DescentTrace.endpoint [] e.path)) ∧
      e.representative = M7.CanonicalOuter.canonical e.leaf ∧
      e.action = M7.CanonicalOuter.realizer e.leaf ∧
      e.leafSignature = M7.RecipeSignature.signature e.leaf ∧
      e.representativeSignature = M7.RecipeSignature.signature e.representative ∧
      e.stabilizer = M7.ActualFactorized.stabilizerNumerator e.representative)

/-- Success at the end requires recomputing an actual zero root residual. -/
def replay {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) :
    Finset (M7.Action.Recipe N) → List (M7.CompactGeneration.Emission N) → Option (Finset (M7.Action.Recipe N))
  | bases, [] => if M7.CompactGeneration.residual w E bases [] = 0 then some bases else none
  | bases, e :: es => if stepPass w E bases e then replay w E (insert e.representative bases) es else none

/-- The advertised final state is checked against the replay from the empty state. -/
def check {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (o : M7.CompactGeneration.Output N) : Bool :=
  match replay w E ∅ o.emitted with
  | none => false
  | some bases => decide (bases = o.finalBases ∧ o.finalResidual = 0 ∧ o.fuelExhausted = false)

/-- Semantic audit trail, not an input assumption for the checker. -/
def FreshFrom {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) :
    Finset (M7.Action.Recipe N) → List (M7.CompactGeneration.Emission N) → Prop
  | _, [] => True
  | bases, e :: es => e.representative ∉ bases ∧ M7.PrefixOrbit.ClassValid w e.representative ∧
      e.leaf ∈ M7.RecoveryPrefix.completed N w E [] ∧ FreshFrom w E (insert e.representative bases) es
end
end M7.GenerationReplay
'''
(p/'M7GenerationReplay.lean').write_text(source);(b/'lean/M7GenerationReplay.lean').write_text(source)
ns='M7.GenerationReplay.';pre='∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ';bs='Finset (M7.Action.Recipe N)';es='List (M7.CompactGeneration.Emission N)';valid='M7.PrefixSector.ValidSector N E → ';good='M7.RecoveryInstance.GoodBases w '
items=[
('step_exact',[],pre+'∀ (bases : '+bs+') (e : M7.CompactGeneration.Emission N), '+ns+'stepPass w E bases e = true ↔ 0 < M7.CompactGeneration.residual w E bases [] ∧ e = M7.CompactGeneration.emission w E bases'),
('replay_terminal_fold',[],pre+'∀ (bases final : '+bs+') (es : '+es+'), '+ns+'replay w E bases es = some final → M7.CompactGeneration.residual w E final [] = 0 ∧ final = es.foldl (fun acc e => insert e.representative acc) bases'),
('replay_sound',['step_exact'],pre+valid+'∀ (bases final : '+bs+') (es : '+es+'), '+good+'bases → '+ns+'replay w E bases es = some final → '+good+'final ∧ '+ns+'FreshFrom w E bases es'),
('fresh_nodup',[],pre+'∀ (bases : '+bs+') (es : '+es+'), '+ns+'FreshFrom w E bases es → (es.map (fun e => e.representative)).Nodup ∧ ∀ e ∈ es, e.representative ∉ bases'),
('run_replay',['step_exact'],pre+'∀ (bases : '+bs+') (fuel : ℕ) (root : ℤ), root = M7.CompactGeneration.residual w E bases [] → (M7.CompactGeneration.run w E fuel bases root).finalResidual = 0 → '+ns+'replay w E bases (M7.CompactGeneration.run w E fuel bases root).emitted = some (M7.CompactGeneration.run w E fuel bases root).finalBases'),
('generate_checked',['run_replay'],pre+valid+ns+'check w E (M7.CompactGeneration.generate (N := N) w E) = true'),
('checked_coverage',['replay_terminal_fold','replay_sound','fresh_nodup'],pre+valid+'0 < w → ∀ o : M7.CompactGeneration.Output N, '+ns+'check w E o = true → '+good+'o.finalBases ∧ '+ns+'FreshFrom w E ∅ o.emitted ∧ (o.emitted.map (fun e => e.representative)).Nodup ∧ (∀ y ∈ M7.RecoveryPrefix.completed N w E [], y ∈ M7.OrbitResidual.covered o.finalBases) ∧ (∀ c : M7.Action.Recipe N, M7.RawCoverage.Queried w E c → M7.CanonicalOuter.canonical c ∈ o.finalBases ∧ ∃ b ∈ o.finalBases, ∃ g : M7.Action.Record N, M7.Action.act g b = c)')]
guide='''Original M7 finite generation-certificate replay, using actual arithmetic residual and recorded Emission fields. No free count oracle or complete transversal premise. step_exact: normalize Bool.and/decide, apply DescentTrace.check_unique and checked depth to identify the recorded path with actual trace; rewrite leaf and other individual fields, destruct Emission to prove equality. Conversely unfold emission and use trace_length/check_trace. replay_terminal_fold: list induction generalizing bases/final, unfold replay, split its actual Boolean check. replay_sound: list induction; step_exact identifies e with actual emission and positive count. CompactCorrectness.residual_eq/emission_eq bridge to RecoveryInstance.insert_good/fresh_leaf. Get ClassValid of inserted representative from GoodBases membership; remaining membership implies root completed membership. FreshFrom records exact sequential freshness, valid class, and queried anchored leaf. fresh_nodup: induction list with arbitrary bases; tail nonmembership in inserted bases proves head absent from mapped tail and all earlier nonmembership. run_replay: induction fuel generalizing bases/root, unfold run and replay, positive branch step_exact rfl and recursive cache; zero/stop branch finalResidual=0 discharges terminal check. generate_checked uses CompactCorrectness.generate_exact and run_replay after unfolding generate. checked_coverage extracts replay result and verified advertised final state; initial empty GoodBases via CompactCorrectness.initial; use replay_sound/terminal/fresh_nodup; CompactCorrectness.residual_eq + RecoveryInstance.root_zero yields anchored coverage. For raw coverage, apply RawCoverage.remaining_coverage: remaining empty follows count_card/card_eq_zero and zero residual; rootCompleted is defeq RecoveryPrefix.completed at empty prefix. Preserve wpositive only on the original raw anchoring conclusion, N=1/even/repeated factors and empty sector. No parser/extraction/runtime requirement or new mathematical hypothesis. Return tactic lines only; no leading by.\n'''+source
g={'title':'M7 actual finite generation certificate replay and coverage','nodes':[{'id':i,'dependencies':d,'spec':{'name':ns+i,'statement':s,'imports':['M7GenerationReplay'],'context':'','queries':['algebra'],'guidance':guide}}for i,d,s in items]}
(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');preflight='import M7GenerationReplay\n'+''.join('def target_'+str(j)+' : Prop := ('+s+')\n'for j,(_,_,s)in enumerate(items));(p/'Preflight.lean').write_text(preflight);(b/'GraphPreflight.lean').write_text(preflight)
src=base/'compact_correctness'
for n in ['lean-toolchain','lake-manifest.json']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
lake='''name = "M7GenerationReplay"
version = "0.1.0"
defaultTargets = ["M7GenerationReplay"]
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
'''
for f in sorted(p.glob('*.lean')):
 if f.stem!='Preflight':lake+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(lake);(b/'lakefile.toml').write_text(lake);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(provenance,indent=2)+'\n')
(b/'SCOPE.md').write_text('Original M7 finite certificate replay: actual positive residual, both child counts and deterministic path, depth, endpoint, canonical representative, realizer, signatures and full stabilizer are recomputed. Sequential insertion starts from empty bases, and success requires actual zero final residual. The checker accepts actual generation and implies sequential freshness, valid classes and final anchored/raw coverage. No trusted numeric/hash oracle, complete transversal premise, parser/extraction/runtime requirement or M8 efficiency gate is introduced.\n')
ctl=Path('/home/jing/m7_canonical_preflight_launch.py').read_text().replace('canonical-block','generation-replay').replace('canonical_block','generation_replay').replace('M7CanonicalBlock','M7GenerationReplay').replace('13 exact','7 exact').replace("env['M7_COMPILE_TIMEOUT']='600'","env['M7_COMPILE_TIMEOUT']='600';env['M7_BROAD_RETRIEVAL']='1'")
c=Path('/home/jing/m7_generation_replay_preflight_launch.py');c.write_text(ctl);(b/'preflight_launch.py').write_text(ctl);shutil.copy2('/home/jing/m7_launch_batch.py',b/'launch_batch.py')
log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(c)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print({'targets':7,'controller_pid':proc.pid})
