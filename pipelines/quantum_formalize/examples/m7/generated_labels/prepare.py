from pathlib import Path
s=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text();head=s.split("source='''",1)[0]
head=head.replace("b=base/'prefix_orbit'","b=base/'generated_labels'").replace('m7-lean-prefix-orbit-formalization','m7-lean-generated-labels-formalization')
head=head.replace("parents=[('residue_prefix','M7ResiduePrefixAccepted'),('actual_signature','M7RecipeSignatureAccepted'),('connectivity','M7ConnectivityAccepted'),('canonical_classes','M7CanonicalClassesAccepted'),('orbit_residual','M7OrbitResidualAccepted')]","parents=[('generated_family','M7GeneratedFamilyAccepted'),('closed_solve','M7ClosedSolveAccepted'),('quality_table','M7QualityTableAccepted')]")
exec(head)
source='''import M7GeneratedFamilyAccepted
import M7ClosedSolveAccepted
import M7QualityTableAccepted

namespace M7.GeneratedLabels
end M7.GeneratedLabels
'''
(p/'M7GeneratedLabels.lean').write_text(source);(b/'lean/M7GeneratedLabels.lean').write_text(source)
src=base/'generated_family'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M7GeneratedLabels"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M7GeneratedLabels"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → '
fam='M7.GeneratedFamily.family N w E';sz='M7.GeneratedFamily.size N w E';r='M7.Action.Recipe N';gen='(M7.CompactGeneration.generate (N := N) w E)';cv='M7.PrefixOrbit.ClassValid w '
items=[
('pointwise',[],f+'∀ i : Fin ('+sz+'), M6.Final.PointwiseCorrect N (M7.Supports.polynomial ('+fam+' i).1) (M7.Supports.polynomial ('+fam+' i).2)'),
('cache',[],f+'∀ (i : Fin ('+sz+')) (g : M7.Action.Record N), (M7.DefaultQuery.dimension (M7.Action.act g ('+fam+' i)), M7.DefaultQuery.distance (M7.Action.act g ('+fam+' i))) = M7.QualityTable.cache ('+fam+' i)'),
('arrays',[],f+'∀ (i : Fin ('+sz+')) (g : M7.Action.Record N), (M7.QualityTable.leftTable ('+fam+' i) (g.unit,g.exchange)).size = N ∧ (M7.QualityTable.rightTable ('+fam+' i) (g.unit,g.exchange)).size = N ∧ M7.QualityTable.placedScores ('+fam+' i) g = (M7.DefaultQuery.locality (M7.Action.act g ('+fam+' i)), M7.DefaultQuery.radius (M7.Action.act g ('+fam+' i)))'),
('witness',[],f+'∀ (i : Fin ('+sz+')) (g : M7.Action.Record N) (d k : ℕ) (v : M6.Pinned.Vector (2*N)), M6.ActualTransfer.solve N (M7.Supports.polynomial ('+fam+' i).1) (M7.Supports.polynomial ('+fam+' i).2) = some (d,v,k) → M7.Transport.distance (M7.Action.act g ('+fam+' i)) = some d ∧ M7.Transport.Xmap g v ∈ M7.Transport.LX (M7.Action.act g ('+fam+' i)) ∧ M6.Pinned.weight (M7.Transport.Xmap g v) = d ∧ M6.Flatten.J N (M7.Transport.Xmap g v) ∈ M7.Transport.LZ (M7.Action.act g ('+fam+' i)) ∧ M6.Pinned.weight (M6.Flatten.J N (M7.Transport.Xmap g v)) = d ∧ k ≤ 2*N')]
guide="Actual generated-class M6 integration, original M7 scope only. GeneratedFamily.family_good supplies cards and connectedness; family_anchored supplies both zero anchors. Apply ClosedSolve.closed_pointwise (sealed full M6 algorithm contract including answer, recurrence, witness, costs), QualityTable.cache_action and array_scores. For witness use Connectivity.anchored_gcd to derive literal Domain gcd=1, then Transport.actual_witness. No free GoodBases, supplied family, distance oracle or AnswerCorrect hypothesis is allowed: all derived from actual generator under original positive weight and valid E. No new algorithm or strengthened requirement. Return tactic lines only.\n"+source
graph={'title':'M7 actual generated-class distance, witness and locality integration','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M7.GeneratedLabels.'+i,'statement':st,'imports':['M7GeneratedLabels'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]}
(b/'graph.json').write_text(json.dumps(graph,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7GeneratedLabels\n'+''.join('def target_'+str(j)+' : Prop := '+st+'\n'for j,(_,_,st)in enumerate(items)));(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n')
ctl=Path('/home/jing/m7_canonical_preflight_launch.py').read_text().replace('canonical-block','generated-labels').replace('canonical_block','generated_labels').replace('M7CanonicalBlock','M7GeneratedLabels').replace('13 exact','4 exact').replace("env['M7_COMPILE_TIMEOUT']='600'","env['M7_COMPILE_TIMEOUT']='600';env['M7_BROAD_RETRIEVAL']='1'")
cp=Path('/home/jing/m7_generated_labels_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m7_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'prepared':len(items),'controller_pid':proc.pid})
