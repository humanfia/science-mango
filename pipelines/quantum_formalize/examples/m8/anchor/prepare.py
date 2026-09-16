from pathlib import Path
s=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text();head=s.split("source='''",1)[0]
head=head.replace("b=base/'prefix_orbit'","b=repo/'pipelines/quantum_formalize/examples/m8/anchor'").replace('m7-lean-prefix-orbit-formalization','m8-lean-anchor-formalization')
head=head.replace("parents=[('residue_prefix','M7ResiduePrefixAccepted'),('actual_signature','M7RecipeSignatureAccepted'),('connectivity','M7ConnectivityAccepted'),('canonical_classes','M7CanonicalClassesAccepted'),('orbit_residual','M7OrbitResidualAccepted')]","parents=[('action','M7ActionAccepted')]")
head=head.replace("p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True)","p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True)")
exec(head)
source='''import M7ActionAccepted

namespace M8.Anchor
abbrev Recipe (N : ℕ) := M7.Action.Recipe N
def left {N : ℕ} (c : Recipe N) (e : Bool) := if e then c.2 else c.1
def right {N : ℕ} (c : Recipe N) (e : Bool) := if e then c.1 else c.2
def Eligible {N : ℕ} (c : Recipe N) (e : Bool) (a b : ZMod N) : Prop :=
  a ∈ left c e ∧ b ∈ right c e
def record {N : ℕ} [NeZero N] (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N) : M7.Action.Record N :=
  ⟨u, e, -((u : ZMod N)*a), -((u : ZMod N)*b)⟩
noncomputable def trial {N : ℕ} [NeZero N] (c : Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N) : Recipe N :=
  M7.Action.act (record e u a b) c
noncomputable def span {N : ℕ} (c : Recipe N) : ℕ :=
  max (c.1.sup ZMod.val) (c.2.sup ZMod.val)
def Anchored {N : ℕ} [NeZero N] (c : Recipe N) : Prop := 0 ∈ c.1 ∧ 0 ∈ c.2
end M8.Anchor
'''
(p/'M8Anchor.lean').write_text(source);(b/'lean/M8Anchor.lean').write_text(source)
src=base/'action'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8Anchor"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8Anchor"]',s,flags=re.M)
for f in sorted(p.glob('*.lean')):
 if f.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), '
t='M8.Anchor.trial c e u a b'
items=[
('trial_formula',[],f+t+' = ((M8.Anchor.left c e).image (fun i => (u : ZMod N)*(i-a)), (M8.Anchor.right c e).image (fun i => (u : ZMod N)*(i-b)))'),
('anchored',[],f+'M8.Anchor.Eligible c e a b → M8.Anchor.Anchored ('+t+')'),
('translation_reconstruction',[], '∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (g : M7.Action.Record N), M8.Anchor.Anchored (M7.Action.act g c) → ∃ a b : ZMod N, M8.Anchor.Eligible c g.exchange a b ∧ M8.Anchor.record g.exchange g.unit a b = g'),
('record_injective',[], '∀ (N : ℕ) [NeZero N] (e : Bool) (u : (ZMod N)ˣ) (a b a1 b1 : ZMod N), M8.Anchor.record e u a b = M8.Anchor.record e u a1 b1 → a = a1 ∧ b = b1'),
('span_le',[], '∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (L : ℕ), M8.Anchor.span c ≤ L ↔ (∀ i ∈ c.1, i.val ≤ L) ∧ (∀ i ∈ c.2, i.val ≤ L)'),
('span_lt_order',[], '∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N), M8.Anchor.span c < N'),
('inverse_trial',[],f+'M7.Action.act (M7.Action.inverse (M8.Anchor.record e u a b)) ('+t+') = c'),
('passing_presentations',['anchored','translation_reconstruction'], '∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (L : ℕ), (∃ (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b ∧ M8.Anchor.span (M8.Anchor.trial c e u a b) ≤ L) ↔ ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) ≤ L')]
guide='Original revised M8 sections2-3 anchor discovery, arbitrary cutoff parameter L in this foundational batch. Actual M7.Action.Record and act; never assume supplied optimal presentation or canonical-minimum span. Image-membership at zero supplies anchors and shift equations; reconstruction record equality uses Record.ext/cases. Unit multiplication is injective even at N=1 (unique residue automorphism). span uses standard residues and finite sup; use ZMod.val_lt. inverse_trial reuses the accepted actual action inverse law. Return tactic lines only, no target/definition edits or new premises.\n'+source
nodes=[{'id':i,'dependencies':deps,'spec':{'name':'M8.Anchor.'+i,'statement':st,'imports':['M8Anchor'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 actual anchor discovery and translation equivalence','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8Anchor\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m7_canonical_preflight_launch.py').read_text().replace('m7-lean-canonical-block','m8-lean-anchor').replace('examples/m7/canonical_block','examples/m8/anchor').replace('M7CanonicalBlock','M8Anchor').replace('13 exact','8 exact').replace("'/home/jing/m7_launch_batch.py','canonical_block','canonical-block','2'","'/home/jing/m8_launch_batch.py','anchor','anchor','2'").replace("env['M7_COMPILE_TIMEOUT']='600'","env['M8_COMPILE_TIMEOUT']='600';env['M8_BROAD_RETRIEVAL']='1'")
cp=Path('/home/jing/m8_anchor_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_anchor.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
