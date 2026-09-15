from pathlib import Path
import json,hashlib,shutil,subprocess
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');base=repo/'pipelines/quantum_formalize/examples/m7';b=base/'overfull_boundary';p=Path('/home/jing/m7-lean-overfull-boundary-formalization');parents=[('compact_correctness','M7CompactCorrectnessAccepted')]
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

/- Original positive-weight empty-domain boundaries; no new input restriction. -/
'''
(p/'M7OverfullBoundary.lean').write_text(source);(b/'lean/M7OverfullBoundary.lean').write_text(source)
ns='M7.OverfullBoundary.';pre='∀ (N w : ℕ) [NeZero N], ';output='M7.CompactGeneration.generate (N := N) w E'
items=[
('class_impossible',[],pre+'N < w → ∀ c : M7.Action.Recipe N, ¬ M7.PrefixOrbit.ClassValid w c'),
('overfull_generate',['class_impossible'],pre+'∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → N < w → ('+output+').finalBases = ∅ ∧ ('+output+').emitted = [] ∧ ('+output+').finalResidual = 0 ∧ ('+output+').fuelExhausted = false'),
('empty_root',[],pre+'0 < w → M7.CompactGeneration.residual (N := N) w ∅ ∅ [] = 0'),
('empty_generate',['empty_root'],pre+'0 < w → (M7.CompactGeneration.generate (N := N) w ∅).finalBases = ∅ ∧ (M7.CompactGeneration.generate (N := N) w ∅).emitted = [] ∧ (M7.CompactGeneration.generate (N := N) w ∅).finalResidual = 0 ∧ (M7.CompactGeneration.generate (N := N) w ∅).fuelExhausted = false')]
guide="Original M7 positive-weight empty-answer boundaries only. class_impossible: Finset.card_le_univ bounds support card by Fintype.card(ZMod N)=N, contradict N<w and ClassValid cardinality. overfull_generate: CompactCorrectness.generate_exact gives GoodBases final, zero residual and false exhausted; ext/membership plus class_impossible forces finalBases=empty. CompactCorrectness.generate_card then gives emitted.length=0, hence emitted=nil. empty_root: unfold CompactGeneration.residual at empty bases and PrefixBits.count, use (PrefixSector.empty_sector N w ...).1. empty_generate: unfold CompactGeneration.generate, rewrite empty_root, simplify Int.toNat_zero and CompactGeneration.run at zero fuel/root. No new restriction, no w=0 classification task, no free count/transversal premise. Return tactic lines only, no leading by.\n"+source
g={'title':'M7 original overfull-weight and empty-sector boundaries','nodes':[{'id':i,'dependencies':d,'spec':{'name':ns+i,'statement':s,'imports':['M7OverfullBoundary'],'context':'','queries':['algebra'],'guidance':guide}}for i,d,s in items]}
(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');preflight='import M7OverfullBoundary\n'+''.join('def target_'+str(j)+' : Prop := ('+s+')\n'for j,(_,_,s)in enumerate(items));(p/'Preflight.lean').write_text(preflight);(b/'GraphPreflight.lean').write_text(preflight)
src=base/'compact_correctness'
for n in ['lean-toolchain','lake-manifest.json']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
lake='''name = "M7OverfullBoundary"
version = "0.1.0"
defaultTargets = ["M7OverfullBoundary"]
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
(b/'SCOPE.md').write_text('Original positive-weight empty-answer boundaries: weights larger than N cannot form ClassValid supports; actual generation therefore emits nothing. An empty signature sector also yields actual empty generation. No w=0 classification, parser/runtime requirement, or extra efficiency gate is introduced.\n')
ctl=Path('/home/jing/m7_canonical_preflight_launch.py').read_text().replace('canonical-block','overfull-boundary').replace('canonical_block','overfull_boundary').replace('M7CanonicalBlock','M7OverfullBoundary').replace('13 exact','4 exact').replace("env['M7_COMPILE_TIMEOUT']='600'","env['M7_COMPILE_TIMEOUT']='600';env['M7_BROAD_RETRIEVAL']='1'")
c=Path('/home/jing/m7_overfull_boundary_preflight_launch.py');c.write_text(ctl);(b/'preflight_launch.py').write_text(ctl);shutil.copy2('/home/jing/m7_launch_batch.py',b/'launch_batch.py')
log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(c)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print({'targets':4,'controller_pid':proc.pid})
