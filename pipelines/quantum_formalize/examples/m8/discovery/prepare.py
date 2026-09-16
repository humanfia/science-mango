from pathlib import Path
s=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text();head=s.split("\nsource='''",1)[0]
head=head.replace("base=repo/'pipelines/quantum_formalize/examples/m7'","base=repo/'pipelines/quantum_formalize/examples/m8'").replace("b=base/'prefix_orbit'","b=base/'discovery'").replace('m7-lean-prefix-orbit-formalization','m8-lean-discovery-formalization')
head=head.replace("parents=[('residue_prefix','M7ResiduePrefixAccepted'),('actual_signature','M7RecipeSignatureAccepted'),('connectivity','M7ConnectivityAccepted'),('canonical_classes','M7CanonicalClassesAccepted'),('orbit_residual','M7OrbitResidualAccepted')]","parents=[('anchor','M8AnchorAccepted'),('cutoff','M8CutoffAccepted'),('finite_search','M8FiniteSearchAccepted')]")
exec(head)
source='''import M8AnchorAccepted
import M8CutoffAccepted
import M8FiniteSearchAccepted

namespace M8.Discovery
structure Choice (N : ℕ) where
  exchange : Bool
  unitIndex : Fin N
  leftAnchor : Fin N
  rightAnchor : Fin N
  deriving DecidableEq, Fintype
abbrev Key (N : ℕ) := Lex (Bool × Lex (Fin N × Lex (Fin N × Fin N)))
def key {N : ℕ} (k : Choice N) : Key N :=
  toLex (k.exchange, toLex (k.unitIndex, toLex (k.leftAnchor,k.rightAnchor)))
noncomputable def unit {N : ℕ} [NeZero N] (k : Choice N) : (ZMod N)ˣ := by
  classical
  exact if h : IsUnit (k.unitIndex.val : ZMod N) then h.unit else 1
noncomputable def action {N : ℕ} [NeZero N] (k : Choice N) : M7.Action.Record N :=
  M8.Anchor.record k.exchange (unit k) (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N)
noncomputable def transformed {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : Choice N) :=
  M7.Action.act (action k) c
noncomputable def Good {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : Choice N) : Prop :=
  IsUnit (k.unitIndex.val : ZMod N) ∧
  M8.Anchor.Eligible c k.exchange (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N) ∧
  M8.Anchor.span (transformed c k) ≤ M8.Cutoff.limit N
/-- Explicit finite Boolean evaluator: gcd test, anchor membership, then numeric residue span. -/
def test {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : Choice N) : Bool :=
  (Nat.gcd k.unitIndex.val N == 1) &&
  ((M8.Anchor.left c k.exchange).sup (fun i => if i.val == k.leftAnchor.val then 1 else 0) == 1) &&
  ((M8.Anchor.right c k.exchange).sup (fun i => if i.val == k.rightAnchor.val then 1 else 0) == 1) &&
  (decide (max
    ((M8.Anchor.left c k.exchange).sup (fun i => (((k.unitIndex.val : ZMod N)*(i-(k.leftAnchor.val : ZMod N))).val)))
    ((M8.Anchor.right c k.exchange).sup (fun i => (((k.unitIndex.val : ZMod N)*(i-(k.rightAnchor.val : ZMod N))).val)))
      ≤ M8.Cutoff.limit N))
noncomputable def atRight {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) (t a : Fin N) : Option (Choice N) := by
  classical
  exact ((M8.FiniteSearch.find (fun b : Fin N =>
    let k : Choice N := ⟨e,t,a,b⟩
    if test c k then some k else none)).1).map Prod.snd
noncomputable def atLeft {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) (t : Fin N) : Option (Choice N) :=
  ((M8.FiniteSearch.find (fun a : Fin N => atRight c e t a)).1).map Prod.snd
noncomputable def atUnit {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) : Option (Choice N) :=
  ((M8.FiniteSearch.find (fun t : Fin N => atLeft c e t)).1).map Prod.snd
noncomputable def discover {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Option (Choice N) :=
  ((M8.FiniteSearch.find (fun e : Fin 2 => atUnit c (decide (e.val = 1)))).1).map Prod.snd
end M8.Discovery
'''
(p/'M8Discovery.lean').write_text(source);(b/'lean/M8Discovery.lean').write_text(source)
src=base/'anchor'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8Discovery"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8Discovery"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), '
items=[('test_spec',[],f+'∀ k : M8.Discovery.Choice N, M8.Discovery.test c k = true ↔ M8.Discovery.Good c k'),('right_none',['test_spec'],f+'∀ (e : Bool) (t a : Fin N), M8.Discovery.atRight c e t a = none ↔ ∀ b : Fin N, ¬ M8.Discovery.Good c ⟨e,t,a,b⟩'),('none_iff',['right_none'],f+'M8.Discovery.discover c = none ↔ ∀ k : M8.Discovery.Choice N, ¬ M8.Discovery.Good c k'),('sound',['test_spec'],f+'∀ k : M8.Discovery.Choice N, M8.Discovery.discover c = some k → M8.Discovery.Good c k'),('anchored',['sound'],f+'∀ k : M8.Discovery.Choice N, M8.Discovery.discover c = some k → M8.Anchor.Anchored (M8.Discovery.transformed c k)'),('cutoff',['sound'],f+'∀ k : M8.Discovery.Choice N, M8.Discovery.discover c = some k → M8.Anchor.span (M8.Discovery.transformed c k) ≤ M8.Cutoff.limit N'),('good_presentations',[],f+'(∃ k : M8.Discovery.Choice N, M8.Discovery.Good c k) ↔ ∃ (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b ∧ M8.Anchor.span (M8.Anchor.trial c e u a b) ≤ M8.Cutoff.limit N'),('complete',['none_iff','good_presentations'],f+'M8.Discovery.discover c ≠ none ↔ ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) ≤ M8.Cutoff.limit N'),('inverse',[],f+'∀ k : M8.Discovery.Choice N, M7.Action.act (M7.Action.inverse (M8.Discovery.action k)) (M8.Discovery.transformed c k) = c'),('lex_first',['sound'],f+'∀ k : M8.Discovery.Choice N, M8.Discovery.discover c = some k → ∀ j : M8.Discovery.Choice N, M8.Discovery.Good c j → M8.Discovery.key k ≤ M8.Discovery.key j')]
guide='Actual revised M8 discovery: four nested first-success cursor loops ordered exchange(false,true), unit residue, left anchor, right anchor. No candidate/orbit list is materialized; ineligible tuples fail the literal test before support-span acceptance. This has the same first eligible tuple as authoritative enumeration; operational counts and bit costs are downstream. First establish test_spec from actual Nat.gcd unit criterion, standard-residue injectivity, Nat indicator Finset.sup and sup-image equalities; test evaluates finite gcd/membership/residue arithmetic rather than a Classical decision oracle. Use FiniteSearch.find_none/find_some for nested Option.map Prod.snd. Bool e enumerated by Fin2 values0,1. Good-presentations represents every ZMod residue and every unit by its standard FinN value; Units.ext, IsUnit.unit_spec and natCast_zmod_val eliminate proof-choice differences even N=1. complete uses Anchor.passing_presentations. For lex_first use the earlier-none property at each nested cursor and nested lex product order, not canonical-representative minimization. Preserve all exact targets.\n'+source
nodes=[{'id':i,'dependencies':deps,'spec':{'name':'M8.Discovery.'+i,'statement':st,'imports':['M8Discovery'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 authoritative actual lexicographic anchor discovery','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8Discovery\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-discovery').replace('examples/m8/anchor','examples/m8/discovery').replace('M8Anchor','M8Discovery').replace('8 exact','10 exact').replace("'anchor','anchor','2'","'discovery','discovery','2'")
cp=Path('/home/jing/m8_discovery_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_discovery.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
