from pathlib import Path
import json
H=Path(__file__).resolve().parent
p='∀ (P : M5.BinaryPolynomial) (hP : P.Monic)'
c='M5.QuotientCharacter.coordinates P hP'
count='(((W.powersetCard k).filter (fun U => AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = z)).card : ℤ)'
rows=[
('character_sign',[],p+' (lam : M5.Character.BinaryVector P.natDegree) (z : AdjoinRoot P), M5.QuotientCharacter.value P hP lam z = 1 ∨ M5.QuotientCharacter.value P hP lam z = -1','Unfold quotient value and binary character. Each bitSign is a power of -1, hence their product is ±1. Preserve dimension zero and its empty product.'),
('coordinates_support_sum',[],p+' (U : Finset ℕ), '+c+' (AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U)) = M5.SubsetCharacter.vectorSum U (fun s => '+c+' (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ s)))','Unfold ofSupport and vectorSum; use quotient algebra map and linear equivalence map_sum. Quotient collisions and all binary cancellations remain valid.'),
('binomial_coefficient',['character_sign'],p+' (W : Finset ℕ) (k : ℕ) (lam : M5.Character.BinaryVector P.natDegree), M5.ArithmeticSubset.binomialTerm P hP W k lam = (M5.SubsetCharacter.signedProduct W (M5.ArithmeticSubset.monomialValue P hP lam)).coeff k','Use accepted M5.Binomial.signed_coefficient_eval with character_sign. The two signedProduct definitions are identical. Symmetrize coefficient formula. Preserve all k including k>W.card.'),
('numerator_exact',['coordinates_support_sum','binomial_coefficient'],p+' (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), M5.ArithmeticSubset.numerator P hP W k z = (2 : ℤ) ^ P.natDegree * '+count,'Use receipt-verified accepted stage14 subset_character_count from imported M5SubsetCountAccepted. Instantiate D=P.natDegree, f(s)=coordinates(mk P (X^s)), target coordinates(z). Rewrite binomial_coefficient. coordinates_support_sum and coordinates.injective identify the filter predicates. Reuse the imported accepted theorem.'),
('n_exact',['numerator_exact'],p+' (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), M5.ArithmeticSubset.n P hP W k z = '+count,'Unfold n, rewrite numerator_exact, cancel integer division by the positive (2:ℤ)^P.natDegree. Preserve P=1, empty W, k=0 and k>W.card.'),
('n_nonnegative',['n_exact'],p+' (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P), 0 ≤ M5.ArithmeticSubset.n P hP W k z','Rewrite n_exact; natural-number cardinality cast to integer is nonnegative.')]
nodes=[]
for id,deps,statement,guidance in rows:
 nodes.append({'id':id,'dependencies':deps,'spec':{'name':'M5.ArithmeticSubset.'+id,'statement':statement,'imports':['M5ArithmeticSubset'],'context':'','queries':['finite character sum subset polynomial coefficient','integer multiplication division cancellation'],'guidance':guidance+' Return tactic lines only without leading by; preserve exact target.'},'metadata':{'source_section':'§2','supports_obligation':'M5.SUBSET_COUNT / M5.BINOM_EVAL','fallback_queries':['addition commutativity']}})
graph={'title':'M5 stage20: exact quotient subset arithmetic n(P,W,k,z)','source':'research/quantum_m5/research_checkpoints/period_residue_arithmetic_law_reviewed/PROOF.md','source_sha256':'a7c0e2ae5f555864340f4b3e6d6674e5b2e74abf382ca5de4d3e5d68da6951a3','scope':'Arithmetic character/binomial sum divided in ℤ equals exact quotient-residue k-subset count; monicity alone. Stage14 count and exact dependency closure imported with verified receipts.','nodes':nodes}
(H/'graph.json').write_text(json.dumps(graph,indent=2)+'\n')
s='import M5ArithmeticSubset\n\n'
for id,_,statement,_ in rows:s+='noncomputable def M5.Stage20Target.'+id+' : Prop :=\n  '+statement+'\n\n#check M5.Stage20Target.'+id+'\n\n'
(H/'lean/GraphPreflight.lean').write_text(s)
Path('/home/jing/m5-lean-arithmetic-subset-formalization/GraphPreflight.lean').write_text(s)
