from pathlib import Path
s=Path('/home/jing/m8_prepare_orbit_span.py').read_text();head=s.split("\nsource='''",1)[0].replace("b=base/'orbit_span'","b=base/'p3_family'").replace('m8-lean-orbit-span','m8-lean-p3-family').replace("parents=[('anchor','M8AnchorAccepted')]","parents=[('physical_bridge','M8PhysicalBridgeAccepted'),('coverage_foundation','M8CoverageFoundationAccepted'),('cutoff','M8CutoffAccepted'),('anchor','M8AnchorAccepted')]")
exec(head)
source='''import M8PhysicalBridgeAccepted
import M8CoverageFoundationAccepted
import M8CutoffAccepted
import M8AnchorAccepted

namespace M8.P3Family
noncomputable def support (N : ℕ) : Finset (ZMod N) := {0,1,2}
noncomputable def recipe (N : ℕ) : M7.Action.Recipe N := (support N,support N)
noncomputable def polynomial : M6.Cyclic.BinaryPolynomial := 1+Polynomial.X+Polynomial.X^2
end M8.P3Family
'''
(p/'M8P3Family.lean').write_text(source);(b/'lean/M8P3Family.lean').write_text(source)
src=base/'physical_bridge'
for n0 in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n0,p/n0);shutil.copy2(src/n0,b/n0)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8P3Family"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8P3Family"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N], 3 ≤ N → '
r='M8.P3Family.'
items=[('support_data',[],f+'('+r+'support N).card = 3 ∧ (0 : ZMod N) ∈ '+r+'support N ∧ (1 : ZMod N) ∈ '+r+'support N'),('literal_polynomial',[],f+'M7.Supports.polynomial ('+r+'support N) = '+r+'polynomial'),('full_direction',['support_data'],f+'M8.CoverageFoundation.FullDirection ('+r+'support N)'),('valid',['support_data','full_direction'],f+'M8.PhysicalBridge.Valid 3 ('+r+'recipe N)'),('span_cutoff',[],f+'M8.Anchor.span ('+r+'recipe N) ≤ M8.Cutoff.limit N'),('divides_modulus',[],'∀ N : ℕ, 3 ∣ N → '+r+'polynomial ∣ M6.Cyclic.modulus N'),('signature',['literal_polynomial','divides_modulus'],f+'3 ∣ N → M7.RecipeSignature.signature ('+r+'recipe N) = '+r+'polynomial'),('nontrivial',[],r+'polynomial ≠ 1 ∧ '+r+'polynomial ≠ 0 ∧ '+r+'polynomial.natDegree = 2')]
guide='Original accepted M8 first admitted family, all N divisible by3 including even orders; never assume squarefree modulus. Prove explicit residue support polynomial and cardinality with N>=3. Consecutive_full gives full direction; connectivity is closure of union of within-block differences so one full direction suffices. Actual identity support span=2 and cutoff min(N-1,log2(N+1))>=2 for N>=3 (Nat.le_log_iff_pow_le). Polynomial p=(1+X+X²) monic and divides X³+1 via (X+1)*p; if3 dividesN use geometric power divisibility over GF2 (sub=add). Since both inputpolys=p, gcd(p,p,M)=p when p dividesM and monic; no multiplicity loss. Nontrivial via coeff2/natDegree; exact definition untouched. Final recognized/distance/nonseparated family theorem is downstream, this batch does not itself close coverage.\n'+source
nodes=[{'id':i,'dependencies':deps,'spec':{'name':r+i,'statement':st,'imports':['M8P3Family'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 all-order trinomial diagonal family literal foundations','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8P3Family\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-p3-family').replace('examples/m8/anchor','examples/m8/p3_family').replace('M8Anchor','M8P3Family').replace("'anchor','anchor','2'","'p3_family','p3-family','2'")
cp=Path('/home/jing/m8_p3_family_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_p3_family.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
