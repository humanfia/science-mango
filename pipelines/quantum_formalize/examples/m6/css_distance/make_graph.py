from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parent
N='M6.CSS.';P='M6.Pinned.';V=N+'Vector m';S=f'Finset ({V})'
sets=f'(BX CX BZ CZ : {S})'
qd=N+'quantumDistance BX CX BZ CZ'
dx=P+'distance ('+N+'logical BX CX)';dz=P+'distance ('+N+'logical BZ CZ)'
base=f'(0 : {V}) ∈ BX → (0 : {V}) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → '
rows=[
('support_bounds',[],f'∀ (m : ℕ) (p : {N}Pauli m), {P}weight p.1 ≤ {N}weight p ∧ {P}weight p.2 ≤ {N}weight p', 'Use filtered-univ set inclusion and Finset.card_le_card, one disjunct for each component.'),
('pure_weights',[],f'∀ (m : ℕ) (v : {V}), {N}weight (v, 0) = {P}weight v ∧ {N}weight (0, v) = {P}weight v', 'Unfold both weights/supports and prove the filtered finite sets equal. Zero functions evaluate to zero.'),
('logical_pauli_components',[],f'∀ (m : ℕ) {sets} (p : {N}Pauli m), p ∈ {N}logicalPaulis BX CX BZ CZ ↔ p.1 ∈ CX ∧ p.2 ∈ CZ ∧ (p.1 ∈ {N}logical BX CX ∨ p.2 ∈ {N}logical BZ CZ)', 'Expand product/filter/sdiff membership and propositional logic. No inclusion hypotheses needed.'),
('quantum_distance_spec',[],f'∀ (m : ℕ) {sets}, ({qd} = none ↔ {N}logicalPaulis BX CX BZ CZ = ∅) ∧ ∀ d : ℕ, ({qd} = some d ↔ (∃ p ∈ {N}logicalPaulis BX CX BZ CZ, {N}weight p = d) ∧ ∀ p ∈ {N}logicalPaulis BX CX BZ CZ, d ≤ {N}weight p)', 'Same finite minimum argument as imported M6.Pinned.distance_spec, but independently over Pauli pairs and physical union-support weight. Split finite nonemptiness and use Finset.min_prime image membership and minimality.'),
('css_distance_min',['support_bounds','pure_weights','logical_pauli_components','quantum_distance_spec'],f'∀ (m : ℕ) {sets}, {base}{qd} = {N}minDistance ({dx}) ({dz})', 'Use M6.Pinned.distance_spec for both component logical sets and quantum_distance_spec for pairs. Each nontrivial pair has a logical component, and support_bounds gives lower bounds. A minimum component yields pure pair (v,0) or (0,v), using zero boundary membership and inclusions. Split component Option distances into none/some; none means empty. Preserve both empty and one empty cases; no nonemptiness assumptions.'),
('involution_distance',[],f'∀ (m : ℕ) (LX LZ : {S}) (J : {V} → {V}), Function.Involutive J → (∀ v, {P}weight (J v) = {P}weight v) → (∀ v, v ∈ LX ↔ J v ∈ LZ) → {P}distance LX = {P}distance LZ', 'Use imported distance_spec; J maps witnesses and lower bounds in both directions because it is involutive and preserves weight. Empty sets correspond as well. Do not posit the distance equality as a premise.'),
('common_quantum_distance',['css_distance_min','involution_distance'],f'∀ (m : ℕ) {sets} (J : {V} → {V}), {base}Function.Involutive J → (∀ v, {P}weight (J v) = {P}weight v) → (∀ v, v ∈ {N}logical BX CX ↔ J v ∈ {N}logical BZ CZ) → {qd} = {dx}', 'Apply css_distance_min, involution_distance to logical sets, then minDistance d d=d by Option cases. This is the genuine Pauli support minimum equality, not a definition.')]
nodes=[{'id':i,'dependencies':ds,'spec':{'name':N+i,'statement':st,'imports':['M6CSSDistance','M6PinnedAccepted'],'context':'','queries':['weight preserving involution minimum distance'],'guidance':gd+' Preserve the exact frozen target, default limits and allowed axioms. Return proof tactic lines without leading by.'},'metadata':{'source_section':'M6 original §1 CSS distance and J isometry','fallback_queries':['finite set cardinality filter']}} for i,ds,st,gd in rows]
source=H.parents[4]/'research/quantum_m6/research_checkpoints/m6_original_gate_closed_20260915/PROOF.md'
g={'title':'M6 actual Pauli support minimum and common CSS distance','source':str(source.relative_to(H.parents[4])),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'scope':'Independently defined Pauli union-support minimum, exact component minimum theorem, and J-isometry common distance. Actual cyclic spaces are instantiated by root.','nodes':nodes}
(H/'graph.json').write_text(json.dumps(g,ensure_ascii=False,indent=2)+'\n')
s='import M6CSSDistance\nimport M6PinnedAccepted\n\n'
for i,ds,st,gd in rows:s+='noncomputable def M6.CSSTarget.'+i+' : Prop :=\n  '+st+'\n\n#check M6.CSSTarget.'+i+'\n\n'
(H/'lean/GraphPreflight.lean').write_text(s)
