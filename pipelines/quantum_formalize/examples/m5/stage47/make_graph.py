from pathlib import Path
import json
H=Path(__file__).resolve().parent
N='M5.ArithmeticResidueRecovery.'
C='M5.ConditionalResidueCount.'
T='M5.signaturePeriod F'
A='∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → '
rows=[
('completion_word_split',[],
 '∀ {α : Type} (k : ℕ) (u : List α) (a : Fin (k - (u.take k).length) → α) (b : Fin (k - (u.drop k).length) → α), u.length ≤ 2*k → ('+N+'completionWord k u a b).length = 2*k ∧ u.IsPrefix ('+N+'completionWord k u a b) ∧ ('+N+'completionWord k u a b).take k = u.take k ++ List.ofFn a ∧ ('+N+'completionWord k u a b).drop k = u.drop k ++ List.ofFn b',
 'Prove lengths of both completed blocks equal k using take/drop lengths and omega. take/drop of concatenation at first-block length give split identities. Prefix property splits on u.length≤k: then drop k u=[], otherwise take k u has length k and a has empty domain. Use list associativity and take_append_drop. Keep α possibly empty.'),
('completion_prefix_card',['completion_word_split'],
 '∀ {α : Type} [Fintype α] [DecidableEq α] (k : ℕ) (u : List α) (Valid : List α → Prop), u.length ≤ 2*k → '+N+'completionCount k u Valid = M5.PrefixPartition.count ('+N+'fullWords (2*k) Valid) u',
 'Establish cardinality bijection via completionWord. A target word v has length2k and extendsu; inverse completions are the portions of v.take k and v.drop k after their selected prefixes, converted to functions on the known remaining lengths. Injectivity uses equal take/drop blocks and cancellation plus List.ofFn injectivity. For surjectivity use prefix u v to prove selected portions agree. Semantic count only; no arithmetic oracle assumption. Use card_bij or subtype equivalence. Avoid change across inferred Decidable instances; identify filters by extensional membership first.'),
('prefix_algebra',[],
 '∀ (T k : ℕ) (p : List (Fin T)) (a : Fin k → Fin T), '+C+'selectedPolynomial (p ++ List.ofFn a) = '+C+'completedPolynomial ('+C+'selectedPolynomial p) a ∧ '+C+'prefixGcd (p ++ List.ofFn a) = Nat.gcd ('+C+'prefixGcd p) (Finset.univ.gcd (fun i : Fin k => (a i).val))',
 'Polynomial identity follows map_append/list.sum_append and sum_ofFn. Gcd identity follows foldr gcd on append and ofFn: use divisibility antisymmetry and every-coordinate characterization if direct fold lemmas inconvenient. Repetitions are retained and k=0 allowed.'),
('completion_feasible',['completion_word_split','prefix_algebra'],
 '∀ (T w : ℕ) (F : M5.BinaryPolynomial) (u : List (Fin T)) (a : Fin ((w-1) - (u.take (w-1)).length) → Fin T) (b : Fin ((w-1) - (u.drop (w-1)).length) → Fin T), u.length ≤ 2*(w-1) → ('+C+'feasible w F (u.take (w-1)) (u.drop (w-1)) a b ↔ '+N+'wordValid w F ('+N+'completionWord (w-1) u a b))',
 'Rewrite word split and prefix_algebra. Unfold selectedGcd and feasible; reassociate and commute Nat.gcd to identify raw-coordinate gcd. Polynomial signature inputs agree exactly, including zero polynomials and cancellations.'),
('oracle_prefix_count',['completion_prefix_card','completion_feasible'],
 A+'∀ (u : List (Fin ('+T+'))), u.length ≤ 2*(w-1) → '+N+'oracle w F u = M5.PrefixPartition.count ('+N+'fullWords (2*(w-1)) ('+N+'wordValid w F)) u',
 'Apply accepted stage42 period_conditionalA_exact cardinality equality. Prefix lengths fit by take/drop arithmetic and omega. Unfold validCompletions guard, match feasibility filter with completionCount using completion_feasible and filter extensionality; apply completion_prefix_card. Preserve exact arithmetic oracle definition.'),
('oracle_initial',[],
 '∀ (w : ℕ) (F : M5.BinaryPolynomial), '+N+'oracle w F [] = M5.ResidueCount.A w F',
 'Unfold arithmetic definitions: selectedPolynomial []=1, prefixGcd []=0, selectedGcd T [] []=T, remaining=w−1, fits true. RSelected with Z=1 equals ROne by the same monicity wrapper. Both divisor/factor sums agree, multiplication square is pow_two. No mathematical assumptions needed, including w=0.'),
('oracle_partition_terminal',['oracle_prefix_count'],
 A+'(∀ (u : List (Fin ('+T+'))), u.length < 2*(w-1) → '+N+'oracle w F u = ∑ a : Fin ('+T+'), '+N+'oracle w F (u ++ [a])) ∧ (∀ (u : List (Fin ('+T+'))), u.length = 2*(w-1) → 0 < '+N+'oracle w F u → '+N+'wordValid w F u)',
 'All members of fullWords have length2k, by mem_image/ofFn length. Apply accepted stage44 count_partition and count_terminal after rewriting oracle_prefix_count for prefixes and children. Terminal positive indicator gives wordValid from filtered membership. No oracle assumptions may remain.'),
('recovery_correct',['oracle_initial','oracle_partition_terminal'],
 A+'0 < M5.ResidueCount.A w F → ∃ u : List (Fin ('+T+')), ('+N+'recover w F).1 = some u ∧ u.length = 2*(w-1) ∧ '+N+'wordValid w F u ∧ ('+N+'recover w F).2 ≤ 2*(w-1)*('+T+')',
 'Instantiate accepted M5.ResidueRecovery.recover_valid with the concrete oracle, wordValid and m=2*(w−1), using oracle_partition_terminal and oracle_initial. The final theorem contains no abstract oracle correctness hypotheses; bound counts arithmetic candidate tests, not wall time.')]
nodes=[{'id':i,'dependencies':d,'spec':{'name':N+i,'statement':s,'imports':['M5ArithmeticResidueRecovery','M5ConditionalResidueCountAccepted','M5ResidueRecoveryAccepted','M5PrefixPartitionAccepted'],'context':'','queries':['List ofFn prefix take drop cardinality bijection','Finset card_bij filter image list length'],'guidance':g+' Return tactic lines only, without leading by.'},'metadata':{'source_section':'§4 concrete residue recovery','fallback_queries':['List take drop append']}} for i,d,s,g in rows]
g={'title':'M5 stage47: concrete arithmetic residue recovery','source':'research/quantum_m5/research_checkpoints/period_residue_arithmetic_law_reviewed/PROOF.md','source_sha256':'a7c0e2ae5f555864340f4b3e6d6674e5b2e74abf382ca5de4d3e5d68da6951a3','scope':'Actual conditional arithmetic A feeds accepted finite residue recovery; prove exact semantic prefix correspondence, partition, terminal correctness, initial value and bounded successful recovery. No abstract oracle-correctness premise.','nodes':nodes}
(H/'graph.json').write_text(json.dumps(g,ensure_ascii=False,indent=2)+'\n')
s='import M5ArithmeticResidueRecovery\n\n'
for i,d,statement,guidance in rows:s+='noncomputable def M5.Stage47Target.'+i+' : Prop :=\n  '+statement+'\n\n#check M5.Stage47Target.'+i+'\n\n'
(H/'lean/GraphPreflight.lean').write_text(s)
(H/'PREFLIGHT.json').write_text(json.dumps({'accepted':False,'ready_for_full_experiment':False,'pending_dependencies':['stage42 canonical accepted experiment'],'targets':8,'proofs_assumed':False},indent=2)+'\n')
