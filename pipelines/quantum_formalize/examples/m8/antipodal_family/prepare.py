from pathlib import Path
s=Path('/home/jing/m8_prepare_orbit_span.py').read_text();head=s.split("\nsource='''",1)[0].replace("b=base/'orbit_span'","b=base/'antipodal_family'").replace('m8-lean-orbit-span','m8-lean-antipodal-family').replace("parents=[('anchor','M8AnchorAccepted')]","parents=[('physical_bridge','M8PhysicalBridgeAccepted'),('coverage_foundation','M8CoverageFoundationAccepted'),('cutoff','M8CutoffAccepted'),('anchor','M8AnchorAccepted')]")
exec(head)
source='''import M8PhysicalBridgeAccepted
import M8CoverageFoundationAccepted
import M8CutoffAccepted
import M8AnchorAccepted

namespace M8.AntipodalFamily
noncomputable def support (N : ℕ) : Finset (ZMod N) := {0,1,((N/2 : ℕ) : ZMod N),((N/2+1 : ℕ) : ZMod N)}
noncomputable def recipe (N : ℕ) : M7.Action.Recipe N := (support N,support N)
noncomputable def polynomial (N : ℕ) : M6.Cyclic.BinaryPolynomial := (1+Polynomial.X)*(1+Polynomial.X^(N/2))
end M8.AntipodalFamily
'''
(p/'M8AntipodalFamily.lean').write_text(source);(b/'lean/M8AntipodalFamily.lean').write_text(source)
src=base/'physical_bridge'
for n0 in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n0,p/n0);shutil.copy2(src/n0,b/n0)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8AntipodalFamily"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8AntipodalFamily"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → '
r='M8.AntipodalFamily.'
power='∀ (v : ℕ), 3 ≤ v → '
items=[
('support_data',[],f+'('+r+'support N).card = 4 ∧ (0 : ZMod N) ∈ '+r+'support N ∧ (1 : ZMod N) ∈ '+r+'support N ∧ ((N/2 : ℕ) : ZMod N) ∈ '+r+'support N'),
('literal_polynomial',[],f+'M7.Supports.polynomial ('+r+'support N) = '+r+'polynomial N'),
('full_direction',['support_data'],f+'M8.CoverageFoundation.FullDirection ('+r+'support N)'),
('valid',['support_data','full_direction'],f+'M8.PhysicalBridge.Valid 4 ('+r+'recipe N)'),
('polynomial_power',[],power+r+'polynomial (2^v) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^(v-1)+1)'),
('modulus_power',[],power+'M6.Cyclic.modulus (2^v) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^v)'),
('divides_modulus',['polynomial_power','modulus_power'],power+r+'polynomial (2^v) ∣ M6.Cyclic.modulus (2^v)'),
('nontrivial',[],f+'('+r+'polynomial N).Monic ∧ '+r+'polynomial N ≠ 1 ∧ '+r+'polynomial N ≠ 0 ∧ ('+r+'polynomial N).natDegree = N/2+1'),
('signature',['literal_polynomial','divides_modulus','nontrivial'], '∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → M7.RecipeSignature.signature ('+r+'recipe N) = '+r+'polynomial N'),
('cutoff_half',[],power+'M8.Cutoff.limit (2^v) = v ∧ v < 2^(v-1)'),
('degree_bound',['nontrivial'],f+'('+r+'polynomial N).degree < (N : WithBot ℕ)')]
guide='''Original revised M8 §9 exact antipodal rejected family N=2^v,v≥3; literal support {0,1,N/2,N/2+1}, polynomial (1+X)*(1+X^(N/2)). Standard residues are distinct and below N for N≥8 even, so support card4 and literal support polynomial matches ring expansion. Consecutive0,1 gives full direction and actual connectivity, then Valid4. polynomial_power: in characteristic2, 1+X^(2^k)=(1+X)^(2^k), using add_pow_char_pow; N/2=2^(v-1), combine powers. modulus_power same Frobenius identity X^(2^v)+1=(X+1)^(2^v). divisibility follows exponent inequality 2^(v-1)+1≤2^v. nontrivial/degree: degree of 1+X is1, degree of 1+X^h is h>0; monic products and natDegree_mul yield h+1, no cancellation of top terms. signature: actual identical literal polynomials p, gcd(p,p,M)=p since monic and p divides M; retain full multiplicity exponent N/2+1. cutoff_half: Nat.log2(2^v+1)=v by 2^v≤2^v+1<2^(v+1); min(N-1,v)=v; v<2^(v-1) for v≥3 by induction, starting3<4. degree_bound from exact natDegree and positive nonzero polynomial. These are foundations; actual all-action rejection and actual distance2 remain downstream geometry/diagonal bridges, neither is assumed. Return tactic lines only, no leading by.\n'''+source

nodes=[{'id':i,'dependencies':deps,'spec':{'name':r+i,'statement':st,'imports':['M8AntipodalFamily'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 exact antipodal power-of-two family literal foundations','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8AntipodalFamily\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-antipodal-family').replace('examples/m8/anchor','examples/m8/antipodal_family').replace('M8Anchor','M8AntipodalFamily').replace("'anchor','anchor','2'","'antipodal_family','antipodal-family','2'")
launch_line="subprocess.run(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python','/home/jing/m8_launch_batch.py','antipodal_family','antipodal-family','2'],cwd=repo,env=env,check=True)"
assert launch_line in ctl
ctl=ctl.replace(launch_line,"while not (repo/'pipelines/quantum_formalize/examples/m8/exclusion_geometry/experiment/MANIFEST.json').exists(): time.sleep(30)\n"+launch_line).replace('8 exact','11 exact')
cp=Path('/home/jing/m8_antipodal_family_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_antipodal_family.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
