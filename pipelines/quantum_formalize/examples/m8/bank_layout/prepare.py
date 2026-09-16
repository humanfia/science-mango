from pathlib import Path
import json,hashlib,shutil,subprocess,re,sys
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');sys.path.insert(0,str(repo));base=repo/'pipelines/quantum_formalize/examples';b=base/'m8/bank_layout';p=Path('/home/jing/m8-lean-bank-layout-formalization');parents=[('m8/actual_optimizer_resources','M8OptimizerResourcesAccepted')]
old=Path('/home/jing/m8_prepare_optimizer_resources.py').read_text();audit=old[old.index('# Canonical proofs'):old.index('common=Path(')];exec(audit)
common=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text();exec(common[common.index('p.mkdir(exist_ok=True)'):common.index("source='''")])
source='''import M8OptimizerResourcesAccepted
namespace M8.BankLayout
/-- Input, original gcd, output witness, cutoff, selected choice, transformed input. -/
def bufferWidths (N : ℕ) : List ℕ := [2*N,N+1,2*N,N+1,1+3*(N+1),2*N]
def registers : List String :=
  ["phase","exchange","unit","leftAnchor","rightAnchor","leftCursor","rightCursor",
   "gcdP","gcdQ","gcdShift","gcdCarry","inverseP","inverseQ","inverseX","inverseY",
   "inverseShift","inverseCarry","residue","product","remainder","spanLeft","spanRight",
   "sourceAddress","targetAddress","bitCursor","wordCursor","layerCursor","startCursor",
   "queryCursor","workCounter","loopCounter","savedIndex"]
def registerBits (N : ℕ) : ℕ := 32*(N+1)
/-- Exactly the existing M6 banks at the fixed public cutoff, reused for every query. -/
noncomputable def bankSlots (N : ℕ) : ℕ :=
  M6.Transfer.solveStorage (M8.Cutoff.limit N) N (M6.EuclidStorage.actualPreprocessStorage N)
noncomputable def payloadSlots (N : ℕ) : ℕ :=
  (bufferWidths N).sum + registers.length * registerBits N + bankSlots N
end M8.BankLayout
'''
(p/'M8BankLayout.lean').write_text(source);(b/'lean/M8BankLayout.lean').write_text(source)
items=[('workspace_monotone',[], '∀ R S N slots : ℕ, R ≤ S → M6.Transfer.solveStorage R N slots ≤ M6.Transfer.solveStorage S N slots'),('payload_bound',[], '∀ (N : ℕ) [NeZero N], M8.BankLayout.payloadSlots N ≤ 20000*(N+1)^3'),('actual_workspace_fits',['workspace_monotone'],'∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.actualSolveStorage N a b ≤ M8.BankLayout.bankSlots N'),('address_bits_bound',['payload_bound'],'∀ (N : ℕ) [NeZero N], (M8.BankLayout.payloadSlots N).size ≤ 32*(N+1)')]
guide='''Explicit reusable layout for the actual revised M8 algorithm. bankSlots uses the original M6 solveStorage at fixed Cutoff.limit, including its true preprocessing slots, trace banks, signed widths, pins and registers; no asymptotic polynomial is defined as allocation. workspace_monotone unfolds solveStorage/pairedQueryStorage/actualTraceStorage/traceStorageModel/width definitions; scatterEventList.length equals card ScatterEvent = 2^R*2*(2*N+1)*3 via state_count and card_prod; gcongr plus pow_le_pow_right₀ (by decide) hRS proves monotonicity. payload_bound uses M6.Transfer.solve_storage_bound at Cutoff.limit<N and actualPreprocessStorage≤512n² (unfold concrete slots/registerBits or preprocess_storage on 0,0,0), then Cutoff.state_bound and explicit buffer/register lengths. actual_workspace_fits is definition + monotonicity. address_bits_bound uses Nat.size_le: 20000*n³<2^(32*n), n=N+1≥1; 20000<2^15 and n<2^n imply n³<2^(3*n), and 15+3*n≤32*n. Keep all N>0 including N=1; no caller-provided allocation or cost oracle. Return tactic lines only.\n'''+source
g={'title':'M8 actual fixed-cutoff reusable memory bank layout','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M8.BankLayout.'+i,'statement':st,'imports':['M8BankLayout'],'context':'','queries':['Nat size power monotonicity'],'guidance':guide},'metadata':{'fallback_queries':['algebra']}}for i,deps,st in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');pre='import M8BankLayout\n'+''.join('def M8.BankTarget.'+i+' : Prop := '+st+'\n'for i,_,st in items);(p/'GraphPreflight.lean').write_text(pre);(b/'lean/GraphPreflight.lean').write_text(pre)
root=base/'m8/cutoff'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(root/n,p/n);shutil.copy2(root/n,b/n)
s=(root/'lakefile.toml').read_text().replace('M8Cutoff','M8BankLayout')
for f in sorted(p.glob('*.lean')):
 if ('[[lean_lib]]\nname = "'+f.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(s);(b/'lakefile.toml').write_text(s);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
for name in ['preflight.py','launch.py','export.py','finish.py']:
 s=(root/name).read_text().replace('m8-lean-cutoff-formalization','m8-lean-bank-layout-formalization').replace('M8Cutoff','M8BankLayout').replace('==8','==4').replace('eight','four').replace('revised M8 cutoff arithmetic targets','revised M8 actual reusable bank layout targets')
 if name=='finish.py':
  a=s.index("(H/'RESULTS.md').write_text(");e=s.index('\nm={',a);s=s[:a]+"(H/'RESULTS.md').write_text('The explicit original M6 banks at fixed cutoff contain every recognized optimizer workspace; whole input/output/control buffers have polynomial payload and binary-address bounds. All original frozen targets and assembly/environment/payload audits passed. This is a concrete allocation contract, not the final execution-cost composition.\\n')"+s[e:]
 (b/name).write_text(s)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(b/'SCOPE.md').write_text('Reserve six actual bit buffers and 32 named bounded control words plus the existing M6 solve banks at the fixed public cutoff. These banks include actual signed widths, trace scatter layout, query registers/pins and concrete Euclid slots, and are reused across all queries. Whole execution initializes this fixed layout once. payloadSlots is the sum of this concrete layout, never the claimed polynomial upper bound. Final discovery/solver execution and sequential scan composition remain downstream.\n');shutil.copy2(__file__,b/'prepare.py');print('prepared 4 bank layout targets')
