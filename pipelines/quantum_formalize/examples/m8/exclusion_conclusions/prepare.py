from pathlib import Path
s=Path('/home/jing/m8_prepare_p3_family.py').read_text();head=s.split("\nsource='''",1)[0].replace("b=base/'p3_family'","b=base/'exclusion_conclusions'").replace('m8-lean-p3-family','m8-lean-exclusion-conclusions')
head=head.replace("parents=[('physical_bridge','M8PhysicalBridgeAccepted'),('coverage_foundation','M8CoverageFoundationAccepted'),('cutoff','M8CutoffAccepted'),('anchor','M8AnchorAccepted')]","parents=[('solver','M8SolverAccepted'),('antipodal_family','M8AntipodalFamilyAccepted'),('exclusion_geometry','M8ExclusionGeometryAccepted'),('diagonal_polynomial','M8DiagonalPolynomialAccepted')]")
exec(head)
import runpy
normalizer=runpy.run_path(str(base/'import_normalization/css_superset.py'))
normalizer['normalize_child'](repo,p,b/'lean',b/'CSS_IMPORT_NORMALIZATION.json')
source='''import M8SolverAccepted
import M8AntipodalFamilyAccepted
import M8ExclusionGeometryAccepted
import M8DiagonalPolynomialAccepted

namespace M8.Exclusion
end M8.Exclusion
'''
(p/'M8Exclusion.lean').write_text(source);(b/'lean/M8Exclusion.lean').write_text(source)
src=base/'solver'
for n0 in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n0,p/n0);shutil.copy2(src/n0,b/n0)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8Exclusion"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8Exclusion"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
r='M8.Exclusion.';A='M8.AntipodalFamily.';S='M8.Solver.';B='M8.PhysicalBridge.'
f='∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → '
rec=A+'recipe N';pow='(Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(N/2+1)'
items=[
('span_rejected',[], '∀ (N : ℕ) [NeZero N] (w : ℕ) (c : M7.Action.Recipe N), 0 < w → '+B+'Valid w c → '+B+'signature c ≠ 1 → (∀ g : M7.Action.Record N, M8.Cutoff.limit N < M8.Anchor.span (M7.Action.act g c)) → '+S+'run c = '+S+'Outcome.unrecognized ('+B+'signature c)'),
('weight_rejected',['span_rejected'],'∀ (N : ℕ) [NeZero N] (w : ℕ) (c : M7.Action.Recipe N), '+B+'Valid w c → '+B+'signature c ≠ 1 → M8.Cutoff.limit N + 1 < w → '+S+'run c = '+S+'Outcome.unrecognized ('+B+'signature c)'),
('antipodal_span',[],f+'∀ g : M7.Action.Record N, M8.Cutoff.limit N < M8.Anchor.span (M7.Action.act g ('+rec+'))'),
('antipodal_distance',[],f+'M7.Transport.distance ('+rec+') = some 2'),
('antipodal_rejected',['span_rejected','antipodal_span'],f+S+'run ('+rec+') = '+S+'Outcome.unrecognized ('+A+'polynomial N)'),
('antipodal_complete',['antipodal_rejected','antipodal_distance'],f+'('+B+'Valid 4 ('+rec+') ∧ '+B+'signature ('+rec+') = '+pow+' ∧ '+S+'run ('+rec+') = '+S+'Outcome.unrecognized ('+pow+') ∧ M7.Transport.distance ('+rec+') = some 2)')]
guide='''Original revised M8 §9 final exclusions, connected to the actual authoritative solver, not merely an abstract recognizer. Preserve branch priority: F=1 is NoLogical, so general overweight Unrecognized includes F≠1. span_rejected: use Solver.unrecognized_exact and OrbitSpan.attained. Valid equal support cards w>0 gives each Nonempty; an attained minimizing actual action turns the all-action strict bound into cutoff<OrbitSpan.value. weight_rejected follows ExclusionGeometry.weight_exclusion, deriving w>0 by omega. antipodal_span: N=2^v, v≥3 gives N≥8, Even N, N=2*(N/2), and N/2=2^(v-1). AntipodalFamily.support_data supplies0 and natural half; hence ExclusionGeometry.Antipodal (N/2) support (witness0). cutoff_half gives cutoff<N/2; instantiate antipodal_exclusion. antipodal_distance: accepted literal_polynomial identifies both input support polynomials with p=AntipodalFamily.polynomial N. Transport.distance unfolds to M6.Final.quantumDistance; expanding its four spaces makes the diagonal target definitionally M8.Diagonal.distance N (Coordinates.coefficients N p). Apply DiagonalPolynomial.distance_two with F=p, using nontrivial for monic/nonzero/not1, degree_bound, dvd_refl, divides_modulus. Full signature from AntipodalFamily.signature, which retains all repeated factors. antipodal_rejected uses actual Valid4 and nontrivial literal signature, then span_rejected and rewrites reported F=p. antipodal_complete combines Valid4, actual Unrecognized, actual physical CSS distance2 and exact full signature power (X+1)^(N/2+1), converting polynomial_power via N=2^v. No free optimizer/orbit/cardinality/physical correctness premise remains in the final concrete clauses. No added w=0, hardness, Clifford, efficiency or M9 gate. Return tactic lines only, no leading by.\n'''+source
nodes=[{'id':i,'dependencies':deps,'spec':{'name':r+i,'statement':st,'imports':['M8Exclusion'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 actual solver overweight and complete antipodal exclusion clauses','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');pre='import M8Exclusion\n'+''.join('def target_'+str(i)+' : Prop := ('+n['spec']['statement']+')\n'for i,n in enumerate(nodes));(p/'Preflight.lean').write_text(pre);(b/'GraphPreflight.lean').write_text(pre)
shutil.copy2(base/'SOURCE.json',b/'SOURCE.json')
(b/'SCOPE.md').write_text('Original revised M8 §9 complete actual solver exclusions. Final concrete antipodal clause covers all N=2^v,v≥3, with Valid4, exact full signature power, actual run=unrecognized carrying that F, and actual physical CSS distance2. General overweight unrecognized retains F≠1 because F=1 takes priority as noLogical. Generic span premise appears only in an intermediate helper and is discharged for the final concrete clauses. No new classifier or free correctness oracle.\n')
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-exclusion-conclusions').replace('examples/m8/anchor','examples/m8/exclusion_conclusions').replace('M8Anchor','M8Exclusion').replace('8 exact','6 exact').replace("'anchor','anchor','2'","'exclusion_conclusions','exclusion-conclusions','2'")
cp=Path('/home/jing/m8_exclusion_conclusions_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_exclusion_conclusions.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
