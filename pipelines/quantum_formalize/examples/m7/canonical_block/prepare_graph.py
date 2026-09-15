from pathlib import Path
import json,shutil,re
p=Path('/home/jing/m7-lean-canonical-block-formalization');b=Path('/home/jing/science-mango-quantum-harness-publish-20260914/pipelines/quantum_formalize/examples/m7/canonical_block');(b/'lean').mkdir(parents=True,exist_ok=True)
f='∀ (N : ℕ) [NeZero N], '
items=[
('shift_identity',[],f+'∀ A : Support N, shift 0 A = A'),
('shift_add',[],f+'∀ (s t : ZMod N) (A : Support N), shift s (shift t A) = shift (s+t) A'),
('shift_card',[],f+'∀ (s : ZMod N) (A : Support N), (shift s A).card = A.card'),
('decode_key',[],f+'∀ A : Support N, decode N (key A) = A'),
('key_injective',['decode_key'],f+'Function.Injective (key (N := N))'),
('best_anchor_member',[],f+'∀ A : Support N, A.Nonempty → bestAnchor A ∈ A'),
('best_key_agrees',[],f+'∀ A : Support N, A.Nonempty → (ofLex (bestKey A)).1 = key (normalize A)'),
('normalize_card',['shift_card'],f+'∀ A : Support N, (normalize A).card = A.card'),
('normalize_anchor',['best_anchor_member'],f+'∀ A : Support N, A.Nonempty → 0 ∈ normalize A'),
('normalize_minimal',['best_key_agrees'],f+'∀ A : Support N, A.Nonempty → ∀ q ∈ A, key (normalize A) ≤ key (shift (-q) A)'),
('anchor_keys_shift',['shift_add'],f+'∀ (s : ZMod N) (A : Support N), (candidates (shift s A)).image (fun v => (ofLex v).1) = (candidates A).image (fun v => (ofLex v).1)'),
('normalize_shift',['normalize_minimal','anchor_keys_shift','key_injective','best_anchor_member','best_key_agrees','shift_card'],f+'∀ (s : ZMod N) (A : Support N), normalize (shift s A) = normalize A'),
('translation_complete',['normalize_shift','shift_add','shift_identity'],f+'∀ A B : Support N, (∃ s : ZMod N, shift s A = B) ↔ normalize A = normalize B')]
source=(p/'M7CanonicalBlock.lean').read_text()
g={'title':'M7 single-block anchor normalization and exact translation invariant','nodes':[{'id':i,'dependencies':d,'spec':{'name':'M7.CanonicalBlock.'+i,'statement':'open M7.CanonicalBlock in '+s,'imports':['M7CanonicalBlock'],'context':'','queries':['addition commutativity'],'guidance':'Prove this exact finite-support statement. Return tactic lines only, no leading by. Source definitions follow as reference, not proof authority. Lex primary key minimizes the sorted values, secondary anchor val only chooses a realizing shift. For translation invariance, anchor key sets coincide by q -> q+s; use minima and key injectivity. Handle empty supports separately. Finset min, sorting and image lemmas suffice.\n'+source}} for i,d,s in items]}
# open ... in is term syntax but ensure explicit context header applies to proposition
for n,(_,_,s) in zip(g['nodes'],items):
 n['spec']['statement']=re.sub(r'\b(Support|shift|key|decode|candidates|bestKey|bestAnchor|normalize)\b', lambda m: 'M7.CanonicalBlock.'+m.group(0), s)
 n['spec']['context']=''
(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n')
(p/'Preflight.lean').write_text('import M7CanonicalBlock\n'+''.join('def target_'+str(j)+' : Prop := '+n['spec']['statement']+'\n'for j,n in enumerate(g['nodes'])))
shutil.copy2(p/'M7CanonicalBlock.lean',b/'lean/M7CanonicalBlock.lean')
for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(p/name,b/name)
(b/'SCOPE.md').write_text('# Single-block canonical normalization\n\n13 exact targets prove normalization over anchors inside one support, retain a realizing shift, and characterize translation equivalence. No two-support Cartesian product is enumerated. Outer unit/exchange canonicalization remains downstream. Empty supports are handled, though original M7 has positive weight. No full M7 acceptance is claimed.\n')
print('prepared',len(items))
