from pathlib import Path
s=Path('/home/jing/m8_prepare_orbit_span.py').read_text();head=s.split("\nsource='''",1)[0].replace("b=base/'orbit_span'","b=base/'p4_family'").replace('m8-lean-orbit-span','m8-lean-p4-family').replace("parents=[('anchor','M8AnchorAccepted')]","parents=[('physical_bridge','M8PhysicalBridgeAccepted'),('coverage_foundation','M8CoverageFoundationAccepted'),('cutoff','M8CutoffAccepted'),('anchor','M8AnchorAccepted')]")
exec(head)
source='''import M8PhysicalBridgeAccepted
import M8CoverageFoundationAccepted
import M8CutoffAccepted
import M8AnchorAccepted

namespace M8.P4Family
noncomputable def support (N : ℕ) : Finset (ZMod N) := {0,1,2,3}
noncomputable def recipe (N : ℕ) : M7.Action.Recipe N := (support N,support N)
noncomputable def polynomial : M6.Cyclic.BinaryPolynomial := 1+Polynomial.X+Polynomial.X^2+Polynomial.X^3
end M8.P4Family
'''
(p/'M8P4Family.lean').write_text(source);(b/'lean/M8P4Family.lean').write_text(source)
src=base/'physical_bridge'
for n0 in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n0,p/n0);shutil.copy2(src/n0,b/n0)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8P4Family"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8P4Family"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N], 8 ≤ N → '
r='M8.P4Family.'
items=[('support_data',[],f+'('+r+'support N).card = 4 ∧ (0 : ZMod N) ∈ '+r+'support N ∧ (1 : ZMod N) ∈ '+r+'support N'),('literal_polynomial',[],f+'M7.Supports.polynomial ('+r+'support N) = '+r+'polynomial'),('full_direction',['support_data'],f+'M8.CoverageFoundation.FullDirection ('+r+'support N)'),('valid',['support_data','full_direction'],f+'M8.PhysicalBridge.Valid 4 ('+r+'recipe N)'),('span_cutoff',[],f+'M8.Anchor.span ('+r+'recipe N) ≤ M8.Cutoff.limit N'),('power_identity',[],r+'polynomial = (Polynomial.X+1)^3'),('divides_four',[],'∀ N : ℕ, 4 ∣ N → '+r+'polynomial ∣ M6.Cyclic.modulus N'),('nontrivial',[],r+'polynomial ≠ 1 ∧ '+r+'polynomial ≠ 0 ∧ '+r+'polynomial.natDegree = 3')]

guide='Original M8 four-consecutive-support diagonal family foundations. Full target later includes every EVEN N>=8; this batch does not assume N divisible by4 for validity/span, and divides_four only supplies an intermediate divisible-by4 case. Final gcd multiplicity min(3,2^v) must still be proved for every even N. Literal support cardinality/poly require distinct residues0,1,2,3; derive val numerals from N>=8. Consecutive_full yields direction; connectivity union closure with full firstblock gives valid. span3 and 3<=log2(N+1) follow8<=N. Poweridentity characteristic2 polynomial ring normalization. (X+1)^4=X^4+1, thus p divides modulus4 and modulusN if4 dividesN. Exact definitions and statements only.\n'+source

nodes=[{'id':i,'dependencies':deps,'spec':{'name':r+i,'statement':st,'imports':['M8P4Family'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 four-term diagonal family literal foundations','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8P4Family\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-p4-family').replace('examples/m8/anchor','examples/m8/p4_family').replace('M8Anchor','M8P4Family').replace("'anchor','anchor','2'","'p4_family','p4-family','2'")
cp=Path('/home/jing/m8_p4_family_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_p4_family.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
