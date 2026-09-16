from pathlib import Path
s=Path('/home/jing/m8_prepare_discovery.py').read_text();head=s.split("\nsource='''",1)[0].replace("b=base/'discovery'","b=base/'discovery_resources'").replace('m8-lean-discovery-formalization','m8-lean-discovery-resources-formalization').replace("parents=[('anchor','M8AnchorAccepted'),('cutoff','M8CutoffAccepted'),('finite_search','M8FiniteSearchAccepted')]","parents=[('discovery','M8DiscoveryAccepted'),('weighted_search','M8WeightedSearchAccepted')]")
exec(head)
source='''import M8DiscoveryAccepted
import M8WeightedSearchAccepted

namespace M8.DiscoveryResources
/-- Symbolic binary-operation upper charges, not Lean evaluator time.
The explicit order bounds residue bit width by N+1.  Membership scans charge
comparison and cursor operations, and span scans charge subtraction,
multiplication, reduction and maximum.  Only executed branches are charged. -/
def control (N : ℕ) : ℕ := 8*(N+1)
def memberCharge {N : ℕ} (A : Finset (ZMod N)) : ℕ :=
  A.sum (fun _ => 4*(N+1))
def spanCharge {N : ℕ} (A : Finset (ZMod N)) : ℕ :=
  A.sum (fun _ => 16*(N+1)^2)
def leftTest {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : M8.Discovery.Choice N) : Bool :=
  ((M8.Anchor.left c k.exchange).sup (fun i => if i.val == k.leftAnchor.val then 1 else 0) == 1)
def rightTest {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : M8.Discovery.Choice N) : Bool :=
  ((M8.Anchor.right c k.exchange).sup (fun i => if i.val == k.rightAnchor.val then 1 else 0) == 1)
def leafCharge {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : M8.Discovery.Choice N) : ℕ :=
  64*(N+1)^2 +
  if Nat.gcd k.unitIndex.val N == 1 then
    memberCharge (M8.Anchor.left c k.exchange) +
    if leftTest c k then
      memberCharge (M8.Anchor.right c k.exchange) +
      if rightTest c k then
        spanCharge (M8.Anchor.left c k.exchange) + spanCharge (M8.Anchor.right c k.exchange)
      else 0
    else 0
  else 0
def charged {n : ℕ} {α : Type} (N : ℕ) (r : M8.WeightedSearch.Run n α) :=
  r.work+r.calls*control N
noncomputable def rightRun {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) (t a : Fin N) :=
  M8.WeightedSearch.find (fun b : Fin N =>
    let k : M8.Discovery.Choice N := ⟨e,t,a,b⟩
    (if M8.Discovery.test c k then some k else none,leafCharge c k))
noncomputable def leftRun {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) (t : Fin N) :=
  M8.WeightedSearch.find (fun a : Fin N =>
    let r := rightRun c e t a
    (r.selected.map Prod.snd,charged N r))
noncomputable def unitRun {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) :=
  M8.WeightedSearch.find (fun t : Fin N =>
    let r := leftRun c e t
    (r.selected.map Prod.snd,charged N r))
noncomputable def run {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) :=
  M8.WeightedSearch.find (fun e : Fin 2 =>
    let r := unitRun c (decide (e.val=1))
    (r.selected.map Prod.snd,charged N r))
noncomputable def work {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) := charged N (run c)
end M8.DiscoveryResources
'''
(p/'M8DiscoveryResources.lean').write_text(source);(b/'lean/M8DiscoveryResources.lean').write_text(source)
src=base/'discovery'
for n0 in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n0,p/n0);shutil.copy2(src/n0,b/n0)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8DiscoveryResources"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8DiscoveryResources"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), '
r='M8.DiscoveryResources.'
items=[('fold_charges',[],'∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)), '+r+'memberCharge A ≤ 4*N*(N+1) ∧ '+r+'spanCharge A ≤ 16*N*(N+1)^2'),('leaf_bound',['fold_charges'],f+'∀ k : M8.Discovery.Choice N, '+r+'leafCharge c k ≤ 128*(N+1)^3'),('right_projection',[],f+'∀ (e : Bool) (t a : Fin N), ('+r+'rightRun c e t a).selected.map Prod.snd = M8.Discovery.atRight c e t a'),('left_projection',['right_projection'],f+'∀ (e : Bool) (t : Fin N), ('+r+'leftRun c e t).selected.map Prod.snd = M8.Discovery.atLeft c e t'),('unit_projection',['left_projection'],f+'∀ e : Bool, ('+r+'unitRun c e).selected.map Prod.snd = M8.Discovery.atUnit c e'),('projection',['unit_projection'],f+'('+r+'run c).selected.map Prod.snd = M8.Discovery.discover c'),('right_bound',['leaf_bound'],f+'∀ (e : Bool) (t a : Fin N), '+r+'charged N ('+r+'rightRun c e t a) ≤ 136*(N+1)^4'),('left_bound',['right_bound'],f+'∀ (e : Bool) (t : Fin N), '+r+'charged N ('+r+'leftRun c e t) ≤ 144*(N+1)^5'),('unit_bound',['left_bound'],f+'∀ e : Bool, '+r+'charged N ('+r+'unitRun c e) ≤ 152*(N+1)^6'),('work_bound',['unit_bound'],f+r+'work c ≤ 320*(N+1)^6')]
guide='Actual four nested discovery cursors with symbolic elementary binary-operation upper charges accumulated on the executed prefix. This is NOT Lean runtime and not a desired polynomial defined as work; work is the actual weighted recursive search. Projections use WeightedSearch.find_projection and congrArg Prod.fst followed by Option.map. Bounds use WeightedSearch.total_bound (charged reverses sum order), Finset.card_le_univ / ZMod.card, sum_const_nat, powers monotonicity and nlinarith. leafCharge branches are nested conditional nonnegative sums; split all ifs and bound by full scans. Standard binary primitive charging convention is explicit; downstream sequential tag-store simulation must be instantiated. Do not replace this with arbitrary total cost oracle.\n'+source
nodes=[{'id':i,'dependencies':deps,'spec':{'name':r+i,'statement':st,'imports':['M8DiscoveryResources'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 actual discovery prefix symbolic bit-charge accounting','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8DiscoveryResources\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-discovery-resources').replace('examples/m8/anchor','examples/m8/discovery_resources').replace('M8Anchor','M8DiscoveryResources').replace('8 exact','10 exact').replace("'anchor','anchor','2'","'discovery_resources','discovery-resources','2'")
cp=Path('/home/jing/m8_discovery_resources_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_discovery_resources.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
