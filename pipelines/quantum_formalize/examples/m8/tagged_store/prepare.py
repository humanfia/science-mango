from pathlib import Path
import json,shutil,re
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');root=repo/'pipelines/quantum_formalize/examples/m8';h=root/'tagged_store';p=Path('/home/jing/m8-lean-tagged-store-formalization');(h/'lean').mkdir(parents=True,exist_ok=True);p.mkdir(exist_ok=True)
src='''import Mathlib

namespace M8.TaggedStore
abbrev Tag := List Bool
abbrev Store := List (Tag × Bool)
def address (n : ℕ) : Tag := n.bits
def recordBits (r : Tag × Bool) : List Bool :=
  r.1.flatMap (fun b => [true,b]) ++ [false,r.2]
def tapeBits (s : Store) : List Bool := s.flatMap recordBits
-- A compared bit or end marker is one primitive Boolean comparison.
def compare : Tag → Tag → Bool × ℕ
  | [], [] => (true,1)
  | [], _::_ => (false,1)
  | _::_, [] => (false,1)
  | a::as, b::bs =>
    if a = b then let q := compare as bs; (q.1,q.2+1)
    else (false,1)
-- Each visited record is scanned in its explicit tagged encoding, then its
-- buffered tag is compared. One extra primitive advances/tests the cursor.
def read (key : Tag) : Store → Option Bool × ℕ
  | [] => (none,1)
  | r::rs =>
    let q := compare key r.1
    let charge := (recordBits r).length + q.2 + 1
    if q.1 then (some r.2,charge)
    else let rest := read key rs; (rest.1,charge+rest.2)
-- This denotes an in-place payload write at the first matching record. The
-- structural returned list is the post-state, not an allocated copy of tape.
def write (key : Tag) (bit : Bool) : Store → Store × ℕ
  | [] => ([],1)
  | r::rs =>
    let q := compare key r.1
    let charge := (recordBits r).length + q.2 + 1
    if q.1 then ((r.1,bit)::rs,charge)
    else let rest := write key bit rs; (r::rest.1,charge+rest.2)
def packFrom (start : ℕ) : List Bool → Store
  | [] => []
  | b::bs => (address start,b)::packFrom (start+1) bs
end M8.TaggedStore
'''
(p/'M8TaggedStore.lean').write_text(src);(h/'lean/M8TaggedStore.lean').write_text(src)
n='M8.TaggedStore.'
items=[
('address_representation',[], 'Function.Injective '+n+'address ∧ ∀ i : ℕ, ('+n+'address i).length = i.size'),
('comparison_exact',[], '∀ a b : '+n+'Tag, ('+n+'compare a b).1 = decide (a=b) ∧ ('+n+'compare a b).2 ≤ a.length+1'),
('read_work',['comparison_exact'],'∀ (B : ℕ) (key : '+n+'Tag) (s : '+n+'Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → ('+n+'read key s).2 ≤ s.length*(4*(B+1))+1'),
('write_work',['comparison_exact'],'∀ (B : ℕ) (key : '+n+'Tag) (bit : Bool) (s : '+n+'Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → ('+n+'write key bit s).2 ≤ s.length*(4*(B+1))+1'),
('write_layout',[], '∀ (key : '+n+'Tag) (bit : Bool) (s : '+n+'Store), (('+n+'write key bit s).1.map Prod.fst) = s.map Prod.fst ∧ ('+n+'tapeBits ('+n+'write key bit s).1).length = ('+n+'tapeBits s).length'),
('packed_layout',['address_representation'],'∀ (start : ℕ) (mem : List Bool), ('+n+'packFrom start mem).length = mem.length ∧ (∀ r ∈ '+n+'packFrom start mem, r.1.length ≤ (start+mem.length).size) ∧ ('+n+'tapeBits ('+n+'packFrom start mem)).length ≤ mem.length*(2*(start+mem.length).size+2)'),
('indexed_read',['address_representation','comparison_exact'],'∀ (start i : ℕ) (mem : List Bool), ('+n+'read ('+n+'address (start+i)) ('+n+'packFrom start mem)).1 = mem[i]?'),
('indexed_write',['address_representation','comparison_exact'],'∀ (start i : ℕ) (bit : Bool) (mem : List Bool), ('+n+'write ('+n+'address (start+i)) bit ('+n+'packFrom start mem)).1 = '+n+'packFrom start (mem.set i bit)')]
guide='''Original M8 common sequential tagged-store primitive model, not a Lean runtime or full extracted-machine implementation. Nat.bits gives real binary tags, with testBit_eq_inth + eq_of_testBit_eq proving injectivity; size_eq_bits_len gives lengths. compare is short-circuit bit comparison. read/write charge the actual visited record's explicit encoding length, actual comparison steps and cursor control; costs are not defined by polynomial envelopes. Induct on the store for work/layout; recordBits length=2*tag.length+2. For indexed_read/write induct on mem generalizing start i; split i zero/succ; address injectivity separates start from start+i+1; align start+(i+1)=(start+1)+i by omega. List.set outside length is unchanged. Packed layout uses address size monotonicity Nat.size_le_size and start+tail lengths. Preserve empty stores, zero addresses, missing indices. Generic layout bounds are intermediate; final M8 must instantiate the actual optimizer/discovery allocation, not assume an oracle. Return tactic lines only.\n'''+src
g={'title':'M8 concrete sequential tagged-bit-store scan primitives','nodes':[{'id':i,'dependencies':deps,'spec':{'name':n+i,'statement':st,'imports':['M8TaggedStore'],'context':'','queries':['Nat bits List set'],'guidance':guide},'metadata':{'fallback_queries':['algebra']}}for i,deps,st in items]};(h/'graph.json').write_text(json.dumps(g,indent=2)+'\n')
pre='import M8TaggedStore\n'+''.join('def M8.TaggedStoreTarget.'+i+' : Prop := '+st+'\n'for i,_,st in items);(p/'GraphPreflight.lean').write_text(pre);(h/'lean/GraphPreflight.lean').write_text(pre)
base=root/'cutoff'
for name in ['lake-manifest.json','lean-toolchain']:shutil.copy2(base/name,p/name);shutil.copy2(base/name,h/name)
s=(base/'lakefile.toml').read_text().replace('M8Cutoff','M8TaggedStore');(p/'lakefile.toml').write_text(s);(h/'lakefile.toml').write_text(s);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
for name in ['preflight.py','launch.py','export.py','finish.py']:
 s=(base/name).read_text().replace('m8-lean-cutoff-formalization','m8-lean-tagged-store-formalization').replace('M8Cutoff','M8TaggedStore').replace('revised M8 cutoff arithmetic targets','revised M8 tagged-store primitive targets')
 if name=='finish.py':
  a=s.index("(H/'RESULTS.md').write_text(");e=s.index('\nm={',a);s=s[:a]+"(H/'RESULTS.md').write_text('Actual binary address tags, bit comparison, measured record scans, in-place post-state layout and indexed read/write projection have passed all frozen targets and full assembly/environment checks. These are the primitive sequential simulation contracts. Full M8 allocation instantiation and operation-sequence accounting remain downstream obligations; no runtime extraction claim is made.\\n')"+s[e:]
 (h/name).write_text(s)
(h/'SCOPE.md').write_text('Concrete binary tags use Nat.bits. Each record encoding marks each address bit with true then terminates with false and one payload bit. read/write scan only their executed prefix; costs add encoded record bits, executed Boolean comparison steps, and cursor control. write denotes an in-place payload mutation, with its functional return only the logical post-state. No recursion-stack or functional-copy runtime claim is made. The finite indexed-memory projection and unchanged tape-layout proof support the original symbolic sequential-store simulation. Final actual M8 allocation/address bounds and total operation sequence remain required downstream; no generic premise becomes a final free oracle.\n')
shutil.copy2(__file__,h/'prepare.py');print('prepared eight tagged-store targets')
