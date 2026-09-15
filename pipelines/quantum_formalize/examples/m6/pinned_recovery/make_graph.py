from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parent
N='M6.Pinned.'
V=N+'Vector m';P=N+'Pins m'
rows=[
('weight_bound',[],f'∀ (m : ℕ) (v : {V}), {N}weight v ≤ m',
 'Unfold weight; filtered-universe cardinality is bounded by univ.card=m. Preserve m=0.'),
('agrees_pin',[],f'∀ (m : ℕ) (P : {P}) (v : {V}) (i : Fin m) (b : ZMod 2), P i = none → ({N}agrees ({N}pin P i b) v ↔ {N}agrees P v ∧ v i = b)',
 'Unfold agrees/pin/Function.update; split coordinates equal to i or distinct. The none hypothesis makes the old constraint at i vacuous. All other coordinates remain unchanged.'),
('enumerator_coeff',[],f'∀ (m : ℕ) (L : Finset ({V})) (P : {P}) (d : ℕ), ({N}enumerator L P).coeff d = {N}count L P d',
 'Use Polynomial.finset_sum_coeff/coeff_X_pow and card_eq_sum_ones with narrow simp only. Both sides count agreed vectors of exact total physical weight, including pinned ones. Avoid broad simp card/sum loops; handle filter equality by explicit membership if inferred instances differ.'),
('count_nonnegative_positive',[],f'∀ (m : ℕ) (L : Finset ({V})) (P : {P}) (d : ℕ), 0 ≤ {N}count L P d ∧ (0 < {N}count L P d ↔ ∃ v ∈ L, {N}agrees P v ∧ {N}weight v = d)',
 'count is the integer cast of a finite filtered cardinality. Use natCast_nonneg, natCast_pos, card_pos, nonempty and filter membership. No nonemptiness assumption is needed.'),
('count_pin_partition',['agrees_pin'],f'∀ (m : ℕ) (L : Finset ({V})) (d : ℕ), {N}partitions (fun P => {N}count L P d)',
 'At a free coordinate every ZMod2 value is exactly0 or1; obtain ∀b:ZMod2,b=0∨b=1 by ordinary decide (not native_decide). The two pin filters are disjoint and their union is the old filter. Apply agrees_pin and finite cardinality additivity, or narrow pointwise indicator sums. Preserve empty L and d outside the weight range.'),
('decode_unique',[],f'∀ (m : ℕ) (P : {P}), {N}assigned P → ∀ v : {V}, ({N}agrees P v ↔ v = {N}decode P)',
 'Every assigned Option is some b; extensionality and Option.getD give the unique vector. Prove both directions coordinatewise. Do not assume any particular pin value or positive dimension.'),
('distance_spec',[],f'∀ (m : ℕ) (L : Finset ({V})), ({N}distance L = none ↔ L = ∅) ∧ ∀ d : ℕ, ({N}distance L = some d ↔ (∃ v ∈ L, {N}weight v = d) ∧ ∀ v ∈ L, d ≤ {N}weight v)',
 'Split finite-set nonemptiness in distance. Use min_prime membership and least-element property of image weight; exact min witness exists. Empty L yields none. A zero-weight member is permitted at this generic level; cycle-minus-boundary later excludes it.'),
('first_positive_distance',['weight_bound','enumerator_coeff','count_nonnegative_positive','distance_spec'],f'∀ (m : ℕ) (L : Finset ({V})), {N}firstPositive m ({N}enumerator L ({N}free m)) = {N}distance L',
 'All vectors agree with free pins. Coefficient positivity iff an L member has that weight, by prior lemmas; every weight lies in List.range(m+1). List.find? over the increasing range therefore returns exactly the minimum in distance_spec, or none if L empty. Use List.find?_range_eq_some and List.find?_range_eq_none, available in Init.Data.List.Nat.Range, with decide_eq_true_eq; these state positivity at i and failure at every j<i. Do not brute-force physical vectors.'),
('choose_properties',[],f'∀ (m : ℕ) (c : {P} → ℤ) (P : {P}) (i : Fin m), {N}refines P ({N}choose c P i).1 ∧ ({N}choose c P i).1 i ≠ none ∧ ({N}choose c P i).2 ≤ 1',
 'Split P i into none/some and the positivity test. An assigned coordinate is skipped with zero queries; a free coordinate is updated once to0 or1. Function.update preserves all existing some constraints.'),
('recover_properties',['choose_properties'],f'∀ (m : ℕ) (c : {P} → ℤ) (P : {P}) (xs : List (Fin m)), {N}refines P ({N}recover c P xs).1 ∧ (∀ i ∈ xs, ({N}recover c P xs).1 i ≠ none) ∧ ({N}recover c P xs).2 ≤ xs.length',
 'Induct xs generalizing P. Compose refines by its coordinatewise definition, preserve already assigned coordinates, and use choose_properties for the new head. Query counts add and are bounded by length. No nodup or distinct-coordinate hypothesis: assigned coordinates are skipped.'),
('recover_positive',[],f'∀ (m : ℕ) (c : {P} → ℤ), {N}partitions c → ∀ (P : {P}) (xs : List (Fin m)), 0 < c P → 0 < c ({N}recover c P xs).1',
 'Induct xs generalizing P. For a free head, partition c P=c(pin0)+c(pin1); if zero branch is not positive, integer order implies one branch positive. Assigned heads preserve P. This is a generic helper only; downstream count and polynomial identities discharge partitions explicitly.'),
('recover_from_counts',['count_nonnegative_positive','count_pin_partition','decode_unique','recover_properties','recover_positive'],f'∀ (m : ℕ) (L : Finset ({V})) (d : ℕ) (c : {P} → ℤ), (∀ P, c P = {N}count L P d) → 0 < c ({N}free m) → let r := {N}recover c ({N}free m) (List.finRange m); {N}decode r.1 ∈ L ∧ {N}weight ({N}decode r.1) = d ∧ r.2 ≤ m',
 'The supplied exact count identity implies partitions by count_pin_partition. Positive recovery count gives an agreed L vector of weightd. recover_properties and mem_finRange assign every coordinate; decode_unique identifies that vector with the returned decode. length_finRange gives ≤m further coefficient queries. The final M6 theorem will instantiate the identity with proven trace coefficients.'),
('solve_exact',['distance_spec','first_positive_distance','recover_from_counts'],f'∀ (m : ℕ) (L : Finset ({V})) (Q : {P} → Polynomial ℤ), (∀ P, Q P = {N}enumerator L P) → ({N}solve Q = none ↔ L = ∅) ∧ ∀ (d : ℕ) (v : {V}) (k : ℕ), {N}solve Q = some (d, v, k) → v ∈ L ∧ {N}weight v = d ∧ (∀ u ∈ L, d ≤ {N}weight u) ∧ k ≤ m',
 'Rewrite Q coefficient and firstPositive using exact polynomial identity. distance_spec gives the minimum and its witness, hence positive free count. Apply recover_from_counts to c(P)=(Q P).coeffd. Split firstPositive/distance Option to establish none iff empty and every returned triple exact minimum witness with querybound. No abstract oracle-correctness hypothesis is left when Q is the actual enumerator or a proved-equal transfer formula.'),
('minimum_witness',['solve_exact'],f'∀ (m : ℕ) (L : Finset ({V})), L.Nonempty → ∃ (d : ℕ) (v : {V}) (k : ℕ), {N}solve ({N}enumerator L) = some (d, v, k) ∧ v ∈ L ∧ {N}weight v = d ∧ (∀ u ∈ L, d ≤ {N}weight u) ∧ k ≤ m',
 'Instantiate solve_exact with Q=enumerator L and reflexive equality. Nonempty rules out none; split the actual solve result and obtain all minimum-witness properties. This concrete finite-enumerator theorem has no oracle-correctness or partition assumption.')]
nodes=[{'id':i,'dependencies':deps,'spec':{'name':N+i,'statement':statement,'imports':['M6Pinned'],'context':'','queries':['finite binary vector weight pinned enumerator coefficient','List find? minimum finite set pin recursive recovery'],'guidance':guidance+' Return tactic lines only without leading by; keep the exact frozen statement and default limits.'},'metadata':{'source_section':'M6 original §5 pinned enumerators and constructive witness','fallback_queries':['finite set cardinality filter']}} for i,deps,statement,guidance in rows]
source=H.parents[4]/'research/quantum_m6/research_checkpoints/m6_original_gate_closed_20260915/PROOF.md'
g={'title':'M6 finite pinned enumerators and minimum witness recovery','source':str(source.relative_to(H.parents[4])),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'scope':'Generic finite binary-vector integer enumerator, exact pinned coefficient counts and minimum witness reconstruction with at most m further paired coefficient queries. Actual transfer equality is discharged at the M6 root, not assumed as its final conclusion. No cyclic linear algebra or transfer construction here.','nodes':nodes}
(H/'graph.json').write_text(json.dumps(g,ensure_ascii=False,indent=2)+'\n')
s='import M6Pinned\n\n'
for i,ds,st,gd in rows:s+='noncomputable def M6.PinnedTarget.'+i+' : Prop :=\n  '+st+'\n\n#check M6.PinnedTarget.'+i+'\n\n'
for D in [H/'lean',Path('/home/jing/m6-lean-pinned-recovery-formalization')]: (D/'GraphPreflight.lean').write_text(s)
