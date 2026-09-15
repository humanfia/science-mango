from pathlib import Path
s=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text();head=s.split("source='''",1)[0]
head=head.replace("b=base/'prefix_orbit'","b=base/'final_resources'").replace('m7-lean-prefix-orbit-formalization','m7-lean-final-resources-formalization')
head=head.replace("parents=[('residue_prefix','M7ResiduePrefixAccepted'),('actual_signature','M7RecipeSignatureAccepted'),('connectivity','M7ConnectivityAccepted'),('canonical_classes','M7CanonicalClassesAccepted'),('orbit_residual','M7OrbitResidualAccepted')]","parents=[('generated_labels','M7GeneratedLabelsAccepted'),('generation_calls','M7GenerationCallsAccepted'),('compact_storage','M7CompactStorageAccepted'),('scalar_work','M7ScalarWorkAccepted'),('streaming_cost','M7StreamingCostAccepted'),('objective_comparison','M7ObjectiveComparisonAccepted')]")
exec(head)
source='''import M7GeneratedLabelsAccepted
import M7GenerationCallsAccepted
import M7CompactStorageAccepted
import M7ScalarWorkAccepted
import M7StreamingCostAccepted
import M7ObjectiveComparisonAccepted

namespace M7.FinalResources
open scoped BigOperators
noncomputable def distanceWork (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) : ℕ :=
  ∑ i : Fin (M7.GeneratedFamily.size N w E),
    M6.ActualTransfer.actualDistanceWork N
      (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1)
      (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2)
/-- Analysis parameter: maximum signed coordinate word length, not a stored action ledger. -/
noncomputable def objectiveBits {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (bases : M7.GlobalQuery.Family H N) : ℕ := by
  classical
  exact 1 + Finset.univ.sup (fun x : M7.GlobalQuery.Index H N =>
    Finset.univ.sup (fun j : Fin q.objectives.length =>
      (M7.GlobalQuery.objective q bases x j).natAbs.size))
/-- Original signed-word comparison model: up to 2(m+1) comparisons per candidate pair,
    charged by the actual maximum signed word width. Labels/preprocessing/output costs
    are separate. This is not a claim about Lean runtime or arbitrary evaluators. -/
noncomputable def comparisonCharge {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (bases : M7.GlobalQuery.Family H N) : ℕ :=
  (M7.StreamingCost.scanWins q bases).inner * (2*(q.objectives.length+1)) * objectiveBits q bases
end M7.FinalResources
'''
(p/'M7FinalResources.lean').write_text(source);(b/'lean/M7FinalResources.lean').write_text(source)
src=base/'generated_labels'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M7FinalResources"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M7FinalResources"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → '
fam='M7.GeneratedFamily.family N w E';sz='M7.GeneratedFamily.size N w E';gen='(M7.CompactGeneration.generate (N := N) w E)';calls='(M7.GenerationCalls.generateMeasured (N := N) w E).2';t0='(1 + '+sz+' * (2*M7.PrefixBits.depth N+1))';a='M7.Supports.polynomial ('+fam+' i).1';c='M7.Supports.polynomial ('+fam+' i).2';span='M6.ActualTransfer.span ('+a+') ('+c+')'
items=[
('generation',[],f+gen+'.finalBases.card = '+sz+' ∧ '+calls+'.root + '+calls+'.children = '+t0+' ∧ '+calls+'.orbitCounts ≤ '+sz+'*'+t0),
('storage',[],f+'M7.CompactStorage.storedCoreBits N ('+sz+') ≤ 16*('+sz+')*N ∧ M7.CompactStorage.storedWithTablesBits N ('+sz+') ≤ 16*('+sz+')*N + 2*('+sz+')*Nat.totient N*N'),
('label_work',[],f+'M7.FinalResources.distanceWork N w E ≤ 50000*N^3 * (∑ i : Fin ('+sz+'), 4^('+span+')) ∧ ∀ i : Fin ('+sz+'), M6.ActualTransfer.actualSolveStorage N ('+a+') ('+c+') ≤ 16384*N^2*2^('+span+')'),
('witness_work',[],f+'∀ (d k : Fin ('+sz+') → ℕ) (v : Fin ('+sz+') → M6.Pinned.Vector (2*N)), (∀ i, M6.ActualTransfer.solve N ('+a+') ('+c+') = some (d i,v i,k i)) → (∑ i : Fin ('+sz+'), M6.ActualTransfer.actualWitnessWork N ('+a+') ('+c+') (k i)) ≤ 200000*N^4 * (∑ i : Fin ('+sz+'), 4^('+span+'))'),
('word_width',[],'∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), ∀ (x : M7.GlobalQuery.Index H N) (j : Fin q.objectives.length), 1 + (M7.GlobalQuery.objective q bases x j).natAbs.size ≤ M7.FinalResources.objectiveBits q bases'),
('comparison',[],f+'∀ q : M7.DefaultQuery.Query, M7.FinalResources.comparisonCharge q ('+fam+') ≤ 2 * (('+sz+') * (2*Nat.totient N*N^2))^2 * (q.objectives.length+1) * M7.FinalResources.objectiveBits q ('+fam+')')]
guide='''Original M7 resource composition on the ACTUAL generated family. No complete-family/count/label oracle. generation uses CompactCorrectness.generate_card, GeneratedFamily.size and GenerationCalls.generate_count. storage specializes the accepted concrete bit-layout bounds; optional full path transcripts and integer bookkeeping remain additional. label_work extracts ExecutionCorrect and StorageCorrect from GeneratedLabels.pointwise and sums actual distance work over the actual Fin family; use Finset.sum_le_sum and mul_sum. witness_work similarly sums only actual successful solve witness work. word_width is two Finset.le_sup applications on finite actual indices/coordinates. comparison uses StreamingCost.scan_bound and record_cardinality, then monotone multiplication and ring normalization. The comparisonCharge is the explicitly declared original signed-word model (actual candidate visits, sequential comparator <=2(m+1), actual maximum word width), not extracted Lean runtime; preprocessing/label evaluation and requested output are separately charged as in the source. No new asymptotic efficiency requirement. ScalarWork prefix bounds and exact separate-mask visits, ObjectiveComparison semantic equivalence and concrete encoding injectivity remain independently imported fields of the final root, not silently inferred from these six summary inequalities. Return tactic lines only.\n'''+source
graph={'title':'M7 original resource composition for actual generated classes','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M7.FinalResources.'+i,'statement':st,'imports':['M7FinalResources'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]}
(b/'graph.json').write_text(json.dumps(graph,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7FinalResources\n'+''.join('def target_'+str(j)+' : Prop := '+st+'\n'for j,(_,_,st)in enumerate(items)));(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n')
ctl=Path('/home/jing/m7_canonical_preflight_launch.py').read_text().replace('canonical-block','final-resources').replace('canonical_block','final_resources').replace('M7CanonicalBlock','M7FinalResources').replace('13 exact','6 exact').replace("env['M7_COMPILE_TIMEOUT']='600'","env['M7_COMPILE_TIMEOUT']='600';env['M7_BROAD_RETRIEVAL']='1'")
cp=Path('/home/jing/m7_final_resources_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m7_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'prepared':len(items),'controller_pid':proc.pid})
