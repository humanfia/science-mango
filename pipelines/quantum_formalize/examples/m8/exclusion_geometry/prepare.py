from pathlib import Path
import hashlib,json,shutil,subprocess
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');src=repo/'pipelines/quantum_formalize/examples/m8/anchor';b=repo/'pipelines/quantum_formalize/examples/m8/exclusion_geometry';p=Path('/home/jing/m8-lean-exclusion-geometry-formalization');b.mkdir(exist_ok=True);(b/'lean').mkdir(exist_ok=True);p.mkdir(exist_ok=True)
m=json.loads((src/'experiment/MANIFEST.json').read_text());m=m.get('files',m);env=json.loads((src/'experiment/environment.json').read_text());r=json.loads((src/'experiment/result.json').read_text());assert all(r[k]for k in ['assembly_accepted','environment_unchanged','experiment_passed'])
for n,h in m.items():assert hashlib.sha256((src/'experiment'/n).read_bytes()).hexdigest()==h,n
files=[]
for f in (src/'lean').glob('*.lean'):
 if f.name not in env:continue
 h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==env[f.name],f
 for dest in [p/f.name,b/'lean'/f.name]:shutil.copy2(f,dest)
 files.append({'file':f.name,'sha256':h})
a=src/'experiment/AcceptedExperiment.lean'
for dest in [p/'M8AnchorAccepted.lean',b/'lean/M8AnchorAccepted.lean']:shutil.copy2(a,dest)
source='''import M8AnchorAccepted

namespace M8.ExclusionGeometry
def Antipodal {N : ℕ} (h : ℕ) (A : Finset (ZMod N)) : Prop :=
  ∃ x : ZMod N, x ∈ A ∧ x + (h : ZMod N) ∈ A
end M8.ExclusionGeometry
'''
for dest in [p/'M8ExclusionGeometry.lean',b/'lean/M8ExclusionGeometry.lean']:dest.write_text(source)
pre='∀ (N : ℕ) [NeZero N], ';D='M8.ExclusionGeometry.';A='M7.Action.';S='M8.Anchor.span '
items=[
('unit_half',[],pre+'∀ (h : ℕ) (u : (ZMod N)ˣ), N = 2*h → (u : ZMod N) * (h : ZMod N) = (h : ZMod N)'),
('pair_affine',['unit_half'],pre+'∀ (h : ℕ) (B : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), N = 2*h → '+D+'Antipodal h B → '+D+'Antipodal h (B.image ('+A+'affine u s))'),
('pair_span',[],pre+'∀ (h : ℕ) (B : Finset (ZMod N)), N = 2*h → '+D+'Antipodal h B → h ≤ B.sup ZMod.val'),
('orbit_pair',['pair_affine'],pre+'∀ (h : ℕ) (c : '+A+'Recipe N) (g : '+A+'Record N), N = 2*h → ('+D+'Antipodal h c.1 ∨ '+D+'Antipodal h c.2) → ('+D+'Antipodal h ('+A+'act g c).1 ∨ '+D+'Antipodal h ('+A+'act g c).2)'),
('orbit_span',['pair_span','orbit_pair'],pre+'∀ (h : ℕ) (c : '+A+'Recipe N) (g : '+A+'Record N), N = 2*h → ('+D+'Antipodal h c.1 ∨ '+D+'Antipodal h c.2) → h ≤ '+S+'('+A+'act g c)'),
('card_sup',[],pre+'∀ B : Finset (ZMod N), B.card ≤ B.sup ZMod.val + 1'),
('weight_orbit_span',['card_sup'],pre+'∀ (w : ℕ) (c : '+A+'Recipe N) (g : '+A+'Record N), c.1.card = w → c.2.card = w → w ≤ '+S+'('+A+'act g c) + 1'),
('weight_exclusion',['weight_orbit_span'],pre+'∀ (w L : ℕ) (c : '+A+'Recipe N), c.1.card = w → c.2.card = w → L+1 < w → ∀ g : '+A+'Record N, L < '+S+'('+A+'act g c)'),
('antipodal_exclusion',['orbit_span'],pre+'∀ (h L : ℕ) (c : '+A+'Recipe N), N = 2*h → ('+D+'Antipodal h c.1 ∨ '+D+'Antipodal h c.2) → L < h → ∀ g : '+A+'Record N, L < '+S+'('+A+'act g c)')]
guide='''Original revised M8 §9 actual orbit span obstructions. Preserve actual units, swap, both independent shifts. No distance/hardness assertion. unit_half: unit representative val is coprime to N=2h hence odd; write val=2k+1, cast and use N=0 in ZMod N. Alternatively use unique nonzero element of additive order2. No odd-N assumption (N=2h is explicit original geometry). pair_affine: affine(x+h)=affine x+h from unit_half; witnesses in image. pair_span: for x and x+h, if h≤x.val use x; otherwise (x+h).val=x.val+h since x.val+h<2h=N, so second residue≥h. Use ZMod.val_add and val_natCast, and Finset.le_sup on membership; NeZero N plus N=2h gives h>0. orbit_pair splits actual Record.exchange and preserves the OR (one block suffices). orbit_span uses pair_span and max left/right. card_sup: injective ZMod.val maps B into Finset.range (B.sup val+1); card_image of injective, Finset.card_le_card, card_range. weight_orbit_span: accepted Action.support_cards implies both image cards=w under equalweight; apply card_sup then max bound. weight_exclusion and antipodal_exclusion by arithmetic/transitivity. General L is the actual finite span threshold input; downstream instantiate fixed Cutoff.limit and literal families. No free count, no tensor/Clifford claim. Tactic lines only, no leading by.\n'''+source

g={'title':'M8 original weight and antipodal orbit exclusion geometry','nodes':[{'id':i,'dependencies':d,'spec':{'name':D+i,'statement':s,'imports':['M8ExclusionGeometry'],'context':'','queries':['algebra'],'guidance':guide}}for i,d,s in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');pr='import M8ExclusionGeometry\n'+''.join('def target_'+str(i)+' : Prop := ('+s+')\n'for i,(_,_,s)in enumerate(items));(p/'Preflight.lean').write_text(pr);(b/'GraphPreflight.lean').write_text(pr)
for n in ['lean-toolchain','lake-manifest.json']:
 f=Path('/home/jing/m8-lean-anchor-formalization')/n
 assert hashlib.sha256(f.read_bytes()).hexdigest()==env[n],n
 for dest in [p/n,b/n]:shutil.copy2(f,dest)
lake='''name = "M8ExclusionGeometry"
version = "0.1.0"
defaultTargets = ["M8ExclusionGeometry"]
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
'''
for f in sorted(p.glob('*.lean')):
 if f.stem!='Preflight':lake+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(lake);(b/'lakefile.toml').write_text(lake);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'parent':'m8/anchor','canonical_files_verified':len(m),'all_parent_gates':True,'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'source_files':files},indent=2)+'\n');shutil.copy2(b.parent/'SOURCE.json',b/'SOURCE.json')
(b/'SCOPE.md').write_text('Original revised M8 §9: actual finite support weight and antipodal span lower bounds under all units, exchanges and independent shifts. General threshold L is instantiated by the fixed cutoff downstream; actual discover rejection remains a separate exact theorem. No claim about distance, complexity hardness or Clifford equivalence.\n')
ctl=(b.parent/'coverage_foundation/preflight_launch.py').read_text().replace('m8-lean-coverage-foundation-formalization','m8-lean-exclusion-geometry-formalization').replace("examples/m8/coverage_foundation'","examples/m8/exclusion_geometry'").replace('M8CoverageFoundation','M8ExclusionGeometry').replace('6 exact','9 exact').replace("'coverage_foundation','coverage-foundation','2'","'exclusion_geometry','exclusion-geometry','2'")
cp=Path('/home/jing/m8_exclusion_geometry_preflight_launch.py');cp.write_text(ctl);(b/'preflight_launch.py').write_text(ctl);shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');shutil.copy2('/home/jing/m8_prepare_exclusion_geometry.py',b/'prepare.py')
with(b/'controller.log').open('a')as log:proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print('preflight PID',proc.pid)
