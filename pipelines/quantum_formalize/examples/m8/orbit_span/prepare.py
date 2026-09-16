from pathlib import Path
s=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text();head=s.split("\nsource='''",1)[0]
head=head.replace("base=repo/'pipelines/quantum_formalize/examples/m7'","base=repo/'pipelines/quantum_formalize/examples/m8'").replace("b=base/'prefix_orbit'","b=base/'orbit_span'").replace('m7-lean-prefix-orbit-formalization','m8-lean-orbit-span-formalization')
head=head.replace("parents=[('residue_prefix','M7ResiduePrefixAccepted'),('actual_signature','M7RecipeSignatureAccepted'),('connectivity','M7ConnectivityAccepted'),('canonical_classes','M7CanonicalClassesAccepted'),('orbit_residual','M7OrbitResidualAccepted')]","parents=[('anchor','M8AnchorAccepted')]")
exec(head)
source='''import M8AnchorAccepted

namespace M8.OrbitSpan
/-- Analysis-only finite set, not materialized by the discovery algorithm. -/
noncomputable def spans {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun g : M7.Action.Record N => M8.Anchor.Anchored (M7.Action.act g c))).image
    (fun g => M8.Anchor.span (M7.Action.act g c))
noncomputable def value {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : ℕ :=
  if h : (spans c).Nonempty then (spans c).min' h else 0
end M8.OrbitSpan
'''
(p/'M8OrbitSpan.lean').write_text(source);(b/'lean/M8OrbitSpan.lean').write_text(source)
src=base/'anchor'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8OrbitSpan"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8OrbitSpan"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), '
valid=f+'c.1.Nonempty → c.2.Nonempty → '
items=[('spans_nonempty',[],valid+'(M8.OrbitSpan.spans c).Nonempty'),('attained',['spans_nonempty'],valid+'∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) = M8.OrbitSpan.value c'),('small_iff',['spans_nonempty'],valid+'∀ L : ℕ, M8.OrbitSpan.value c ≤ L ↔ ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) ≤ L'),('anchor_minimum',['small_iff'],valid+'∀ L : ℕ, M8.OrbitSpan.value c ≤ L ↔ ∃ (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b ∧ M8.Anchor.span (M8.Anchor.trial c e u a b) ≤ L'),('less_than_order',['attained'],valid+'M8.OrbitSpan.value c < N')]
guide='Original M8 R_orb minimum, analysis-only. The runtime discovery does not calculate/store this Finset or receive a minimum-span oracle. Nonempty supports give arbitrary anchors with e=false,u=1, actual Anchor.anchored. Finset.min membership/min_le supplies attained/small iff, Anchor.passing_presentations equates the anchor and translation parameterizations. span_lt_order gives final bound. Preserve exact original nonempty domain and actual action. Tactic lines only.\n'+source
nodes=[{'id':i,'dependencies':deps,'spec':{'name':'M8.OrbitSpan.'+i,'statement':st,'imports':['M8OrbitSpan'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 exact minimum orbit-span predicate for semantic acceptance','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8OrbitSpan\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-orbit-span').replace('examples/m8/anchor','examples/m8/orbit_span').replace('M8Anchor','M8OrbitSpan').replace('8 exact','5 exact').replace("'anchor','anchor','2'","'orbit_span','orbit-span','2'")
cp=Path('/home/jing/m8_orbit_span_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_orbit_span.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
