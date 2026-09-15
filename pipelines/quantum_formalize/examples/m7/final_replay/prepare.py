from pathlib import Path
s=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text();head=s.split("source='''",1)[0]
head=head.replace("b=base/'prefix_orbit'","b=base/'final_replay'").replace('m7-lean-prefix-orbit-formalization','m7-lean-final-replay-formalization')
head=head.replace("parents=[('residue_prefix','M7ResiduePrefixAccepted'),('actual_signature','M7RecipeSignatureAccepted'),('connectivity','M7ConnectivityAccepted'),('canonical_classes','M7CanonicalClassesAccepted'),('orbit_residual','M7OrbitResidualAccepted')]","parents=[('final_selector','M7FinalSelectorAccepted'),('generated_labels','M7GeneratedLabelsAccepted'),('generation_replay','M7GenerationReplayAccepted'),('label_replay','M7LabelReplayAccepted'),('factor_replay','M7FactorReplayAccepted'),('query_certificate','M7QueryCertificateAccepted')]")
exec(head)
source='''import M7FinalSelectorAccepted
import M7GeneratedLabelsAccepted
import M7GenerationReplayAccepted
import M7LabelReplayAccepted
import M7FactorReplayAccepted
import M7QueryCertificateAccepted

namespace M7.FinalReplay
structure Certificate (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) where
  generation : M7.CompactGeneration.Output N
  factors : List (M5.BinaryPolynomial × ℕ)
  labels : Fin (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)) → M7.LabelReplay.Certificate N
  query : M7.QueryCertificate.Certificate (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)) N
/-- Finite component checks, with explicit alignment of the certified bases and the
    actual deterministic family used by the query indices. No recorded number or hash
    replaces arithmetic recomputation. Query-certificate expansion is explicitly finite. -/
noncomputable def check {N w : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (c : Certificate N w q) : Except M7.DefaultQuery.QueryError Bool := by
  classical
  exact if M7.DefaultQuery.valid N q then
    .ok (M7.GenerationReplay.check w (M7.QuerySectors.effective N q) c.generation &&
      M7.FactorReplay.check (M6.Cyclic.modulus N) c.factors &&
      decide (c.generation.finalBases = (M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)).finalBases) &&
      M7.QueryCertificate.allOn Finset.univ (fun i =>
        M7.LabelReplay.check (M7.FinalSelector.family N w q i) (c.labels i)) &&
      match M7.QueryCertificate.check q (M7.FinalSelector.family N w q) c.query with
      | .ok result => result
      | .error _ => false)
    else .error .invalidSignature
end M7.FinalReplay
'''
(p/'M7FinalReplay.lean').write_text(source);(b/'lean/M7FinalReplay.lean').write_text(source)
src=base/'final_selector'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M7FinalReplay"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M7FinalReplay"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), ';cert='M7.FinalReplay.Certificate N w q';sz='M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)';fam='M7.FinalSelector.family N w q';checked='M7.FinalReplay.check q c = Except.ok true';context=f+'0 < w → w ≤ N → ∀ c : '+cert+', '+checked+' → '
items=[
('parts',[],f+'∀ c : '+cert+', ('+checked+' ↔ M7.DefaultQuery.valid N q ∧ M7.GenerationReplay.check w (M7.QuerySectors.effective N q) c.generation = true ∧ M7.FactorReplay.check (M6.Cyclic.modulus N) c.factors = true ∧ c.generation.finalBases = (M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)).finalBases ∧ (∀ i, M7.LabelReplay.check ('+fam+' i) (c.labels i) = true) ∧ M7.QueryCertificate.check q ('+fam+') c.query = Except.ok true)'),
('exists_certificate',['parts'],f+'0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∃ c : '+cert+', '+checked),
('checked_sets',['parts'],context+'c.query.winners = M7.GlobalQuery.winners q ('+fam+') ∧ c.query.presentations = M7.QueryCertificate.allPresentations q ('+fam+')'),
('raw_winners',['checked_sets'],context+'∀ y : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q y ↔ ∃ x ∈ c.query.winners, M7.FinalSelector.realize q x = y'),
('raw_presentations',['checked_sets'],context+'∀ y : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q y ↔ ∃! x : M7.FinalSelector.Index N w q, x ∈ c.query.presentations ∧ M7.FinalSelector.realize q x = y'),
('physical_labels',['parts'],context+'∀ i : Fin ('+sz+'), ((c.labels i).answer = none ↔ (M7.RecipeSignature.signature ('+fam+' i)).natDegree = 0) ∧ (∀ (d k : ℕ) (v : M6.Pinned.Vector (2*N)), (c.labels i).answer = some (d,v,k) → M7.DefaultQuery.distance ('+fam+' i) = some d ∧ v ∈ M7.Transport.LX ('+fam+' i) ∧ M6.Pinned.weight v = d ∧ M6.Flatten.J N v ∈ M7.Transport.LZ ('+fam+' i) ∧ M6.Pinned.weight (M6.Flatten.J N v) = d ∧ k ≤ 2*N)'),
('invalid_rejection',[],f+'¬ M7.DefaultQuery.valid N q → ∀ c : '+cert+', M7.FinalReplay.check q c = Except.error M7.DefaultQuery.QueryError.invalidSignature')]
guide='''Original M7 complete finite replay composition. parts unfolds only the concrete Boolean conjunction and actual query Except result; use QueryCertificate.allOn_spec. Do not replace a finite component checker by its correctness proposition. exists_certificate constructs actual CompactGeneration.generate, FactorReplay.expected on modulus, LabelReplay.expected for each ACTUAL generated class, and obtains the finite domination witnesses from QueryCertificate.check_exact with actual winners and allPresentations. Use GenerationReplay.generate_checked, FactorReplay.self_check (monic/nonzero modulus), and LabelReplay.self_check; exact factor lemma names can be found in accepted interfaces. checked_sets applies QueryCertificate.check_sound. raw_winners connects GlobalQuery.winners via StreamingIndices.stream_winners and FinalSelector.raw_output; raw_presentations uses FinalSelector.presentation_exact, actual present definition and allPresentations membership. physical_labels derives valid E from QuerySectors.effective_valid, actual equal cards/connectedness and anchors from GeneratedFamily, then LabelReplay.checked_physical_answer. No supplied transversal, correctness oracle or hashes. The base equality is an explicit finite check aligning certificate generation with the deterministic family actually queried. All original positive weight, invalid-query, multiplicities, NoLogical and ties remain. No extra implementation/extraction/runtime goal. Return tactic lines only.\n'''+source
graph={'title':'M7 complete concrete certificate replay and raw-output soundness','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M7.FinalReplay.'+i,'statement':st,'imports':['M7FinalReplay'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]}
(b/'graph.json').write_text(json.dumps(graph,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7FinalReplay\n'+''.join('def target_'+str(j)+' : Prop := '+st+'\n'for j,(_,_,st)in enumerate(items)));(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n')
ctl=Path('/home/jing/m7_canonical_preflight_launch.py').read_text().replace('canonical-block','final-replay').replace('canonical_block','final_replay').replace('M7CanonicalBlock','M7FinalReplay').replace('13 exact','7 exact').replace("env['M7_COMPILE_TIMEOUT']='600'","env['M7_COMPILE_TIMEOUT']='600';env['M7_BROAD_RETRIEVAL']='1'")
cp=Path('/home/jing/m7_final_replay_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m7_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'prepared':len(items),'controller_pid':proc.pid})
