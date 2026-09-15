from pathlib import Path
import json
H=Path(__file__).resolve().parent
p='M5.ResidueCount.'
assume='0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → '
exists='∃ a b : Fin (w-1) → Fin T, '+p+'feasible F a b'
rows=[
('two_block_R_count',['stage29_restricted_R_pending'],'∀ (P : M5.BinaryPolynomial) (T d k : ℕ), P.Monic → 0 < T → d ∣ T → '+p+'ROne P T d k ^ 2 = ∑ a : Fin k → Fin T, ∑ b : Fin k → Fin T, (@ite ℤ (((∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ '+p+'tailPolynomial a) ∧ ((∀ i : Fin k, d ∣ (b i).val) ∧ P ∣ '+p+'tailPolynomial b)) (Classical.propDecidable _) 1 0)',
 'Requires receipt-verified accepted stage29 restricted_R_count before scheduling. Unfold total monicity wrapper; rewrite R as restrictedCount. Expand the square of a filtered cardinality into the double sum of product indicators. Definitions tailPolynomial and restrictedCount agree literally. Preserve empty tails and all repeated/cancelled residues.'),
('pair_indicator_exact',[],'∀ (T k : ℕ) (F : M5.BinaryPolynomial) (a b : Fin k → Fin T), 0 < T → F.Monic → F ∣ M5.cyclicModulus T → '+p+'pairIndicator F a b = (@ite ℤ ('+p+'feasible F a b) (Classical.propDecidable _) 1 0)',
 'Combine accepted stage23 exact_signature_indicator with stage9 connected_indicator/support_divisor_filter. For integer gcd one may use residueSupport=insert0(image tuple values), gcd_image and gcd_insert, or prove divisor equivalence directly by Finset.dvd_gcd_iff. Repetition changes neither gcd nor divisibility; polynomial cancellations must not alter the raw-coordinate gcd. Do not use the polynomial support as the integer gcd domain.'),
('arithmetic_indicator_expansion',['two_block_R_count'],'∀ (T w : ℕ) (F : M5.BinaryPolynomial), '+assume+p+'rawA T w F = ∑ a : Fin (w-1) → Fin T, ∑ b : Fin (w-1) → Fin T, '+p+'pairIndicator F a b',
 'Unfold rawA and use two_block_R_count. A divisor of positive T is positive. Each residual factor is monic by accepted stage23 residual_factors_regular; hence F times its subset product is monic. Swap the finite d,S,a,b sums and factor independent indicator terms to recover pairIndicator. Only finite factor and character arithmetic defines rawA; tuple sums occur on the semantic theorem RHS.'),
('exact_rawA',['arithmetic_indicator_expansion','pair_indicator_exact'],'∀ (T w : ℕ) (F : M5.BinaryPolynomial), '+assume+p+'rawA T w F = ('+p+'validTailPairs T w F).card',
 'Rewrite the arithmetic indicator expansion and every pair_indicator_exact. Finset product/univ and card_filter turn the indicator double sum into validTailPairs.card cast to integers. Do not impose distinctness or require nonzero block polynomials.'),
('rawA_nonnegative_and_positive',['exact_rawA'],'∀ (T w : ℕ) (F : M5.BinaryPolynomial), '+assume+'(0 ≤ '+p+'rawA T w F ∧ (0 < '+p+'rawA T w F ↔ '+exists+'))',
 'Use exact_rawA: a natural-cardinality cast is nonnegative and is positive iff its filtered finite set is nonempty. Unpack pair membership to two tails. Preserve k=0 (w=1), F=1 and all cancellations.'),
('period_A_exact',['exact_rawA','rawA_nonnegative_and_positive'],'∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → '+p+'A w F = ('+p+'validTailPairs (M5.signaturePeriod F) w F).card ∧ 0 ≤ '+p+'A w F ∧ (0 < '+p+'A w F ↔ ∃ a b : Fin (w-1) → Fin (M5.signaturePeriod F), '+p+'feasible F a b)',
 'Use accepted period_law to obtain T>0 and F|M_T at T=signaturePeriod F; then unfold A and instantiate exact_rawA and rawA_nonnegative_and_positive. No additional period-size, squarefree, nonzero-block or weight-upper-bound assumption is allowed.')]
nodes=[{'id':'stage29_restricted_R_pending','dependencies':[],'spec':None,'metadata':{'status':'pending_accepted_dependency_import','required_theorem':'M5.AnchoredTupleCount.restricted_R_count','source_stage':'stage29','unblock_rule':'Verify completed stage29 accepted receipts and exact proof closure before promoting import and removing this gate.'}}]
for id,deps,statement,guidance in rows:
 nodes.append({'id':id,'dependencies':deps,'spec':{'name':p+id,'statement':statement,'imports':['M5ResidueCount'],'context':'','queries':['finite sum product indicator cardinality','Finset gcd image divisibility moebius'],'guidance':guidance+' Return tactic lines only without leading by; preserve exact target.'},'metadata':{'source_section':'§4','supports_obligation':'M5.RESIDUE_COUNT / M5.OCCURRENCE','fallback_queries':['addition commutativity']}})
g={'title':'M5 stage31: original arithmetic residue occurrence count A','source':'research/quantum_m5/research_checkpoints/period_residue_arithmetic_law_reviewed/PROOF.md','source_sha256':'a7c0e2ae5f555864340f4b3e6d6674e5b2e74abf382ca5de4d3e5d68da6951a3','scope':'Exact finite d-divisor and residual-factor-subset arithmetic A equals feasible anchored tail-pair count; no tuple enumeration in arithmetic definition. Stage29 proof import pending.','nodes':nodes}
(H/'graph.json').write_text(json.dumps(g,indent=2)+'\n')
s='import M5ResidueCount\n\n'
for id,_,statement,_ in rows:s+='noncomputable def M5.Stage31Target.'+id+' : Prop :=\n  '+statement+'\n\n#check M5.Stage31Target.'+id+'\n\n'
for root in [H/'lean',Path('/home/jing/m5-lean-residue-count-formalization')]: (root/'GraphPreflight.lean').write_text(s)
