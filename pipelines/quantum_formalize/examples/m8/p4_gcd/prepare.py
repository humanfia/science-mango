from pathlib import Path
s=Path('/home/jing/m8_prepare_orbit_span.py').read_text();head=s.split("\nsource='''",1)[0].replace("b=base/'orbit_span'","b=base/'p4_gcd'").replace('m8-lean-orbit-span','m8-lean-p4-gcd').replace("parents=[('anchor','M8AnchorAccepted')]","parents=[('p4_family','M8P4FamilyAccepted')]")
exec(head)
source='''import M8P4FamilyAccepted

namespace M8.P4Gcd
noncomputable def oddCofactor (m : ℕ) : M6.Cyclic.BinaryPolynomial :=
  ∑ i ∈ Finset.range (2*m+1), Polynomial.X^(2*i)
end M8.P4Gcd
'''

(p/'M8P4Gcd.lean').write_text(source);(b/'lean/M8P4Gcd.lean').write_text(source)
src=base/'p4_family'
for n0 in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n0,p/n0);shutil.copy2(src/n0,b/n0)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8P4Gcd"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8P4Gcd"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N], 8 ≤ N → '
r='M8.P4Gcd.'
items=[('factorization',[],'∀ m : ℕ, M6.Cyclic.modulus (4*m+2) = (Polynomial.X+1)^2 * M8.P4Gcd.oddCofactor m'),('cofactor_eval',[],'∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1'),('cofactor_coprime',['cofactor_eval'],'∀ m : ℕ, IsCoprime (Polynomial.X+1) (M8.P4Gcd.oddCofactor m)'),('gcd_two_mod_four',['factorization','cofactor_coprime'],'∀ m : ℕ, gcd M8.P4Family.polynomial (M6.Cyclic.modulus (4*m+2)) = (Polynomial.X+1)^2'),('signature_even',['gcd_two_mod_four'],f+'Even N → M7.RecipeSignature.signature (M8.P4Family.recipe N) = if 4 ∣ N then M8.P4Family.polynomial else (Polynomial.X+1)^2'),('full_multiplicity',['signature_even'],f+'∀ v m : ℕ, 0 < v → Odd m → N = 2^v*m → M7.RecipeSignature.signature (M8.P4Family.recipe N) = (Polynomial.X+1)^(min 3 (2^v))')]

guide='Exact M8 full even-order multiplicity, no radical and no restriction to4-divisible orders. oddCofactor is the literal geometric sum of powers X² with odd length2m+1. Geometric-sum telescoping gives modulus(4m+2)=(X+1)² H over GF2, and H(1)=1 gives coprimality with X+1. Thus gcd((X+1)³,(X+1)²H)=(X+1)² by normalized monic gcd/common-factor and coprime. For evenN either4 dividesN or N=4m+2 (Nat.mod_add_div, omega); use parent divides_four for former, both literal inputs equal parent polynomial. Finally N=2^v*m with Oddm implies4 dividesN iff2<=v whenv>0; v1 gives exponent2, v>=2 exponent3, min formula follows power monotonicity. Preserve exact hypotheses, all-even domain and no free multiplicity assertion.\n'+source

nodes=[{'id':i,'dependencies':deps,'spec':{'name':r+i,'statement':st,'imports':['M8P4Gcd'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 full repeated-factor gcd at every even order','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8P4Gcd\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-p4-gcd').replace('examples/m8/anchor','examples/m8/p4_gcd').replace('M8Anchor','M8P4Gcd').replace('8 exact','6 exact').replace("'anchor','anchor','2'","'p4_gcd','p4-gcd','2'")
cp=Path('/home/jing/m8_p4_gcd_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_p4_gcd.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
