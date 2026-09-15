import FrozenTarget_d5e8e6cccfba77ff
theorem M5.ConditionalResidueCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), _
  intro T w F p q hT hw hF hFT
  have hmonic (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset) :
      (F * ∏ P ∈ S, P).Monic := by
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro P hP
    exact (M5.PolynomialIndicator.residual_factors_regular F T hT hF hFT P
      (Finset.mem_powerset.mp hS hP)).1
  have hcount (d : ℕ)
      (hd : d ∈ (M5.ConditionalResidueCount.selectedGcd T p q).divisors)
      (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset) :
      M5.ConditionalResidueCount.RSelected (F * ∏ P ∈ S, P)
          (M5.ConditionalResidueCount.selectedPolynomial p) T d
          (M5.ConditionalResidueCount.remaining w p) *
        M5.ConditionalResidueCount.RSelected (F * ∏ P ∈ S, P)
          (M5.ConditionalResidueCount.selectedPolynomial q) T d
          (M5.ConditionalResidueCount.remaining w q) =
        ∑ a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T,
          ∑ b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T,
            M5.ConditionalResidueCount.divisibilityIndicator
              (F * ∏ P ∈ S, P)
              (M5.ConditionalResidueCount.selectedPolynomial p)
              (M5.ConditionalResidueCount.selectedPolynomial q) d a b := by
    apply M5.ConditionalResidueCount.selected_R_pair_count
    · exact hmonic S hS
    · exact hT
    · exact ((M5.ConditionalResidueCount.prefix_gcd_divisibility T d p q).mp
        (Nat.mem_divisors.mp hd).1).1
  unfold M5.ConditionalResidueCount.rawConditionalA
  simp only [mul_assoc]
  simp (disch := assumption) only [hcount]
  unfold M5.ConditionalResidueCount.pairIndicator
    M5.PolynomialIndicator.factorExclusionSum
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_ite_irrel]
  conv_lhs =>
    arg 2
    ext d
    rw [Finset.sum_comm]
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  first
  | skip
  | rw [Finset.sum_comm]
  first
  | (apply Finset.sum_congr rfl
     intro d hd
     apply Finset.sum_congr rfl
     intro S hS)
  | (rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro S hS
     apply Finset.sum_congr rfl
     intro d hd)
  unfold M5.ConditionalResidueCount.divisibilityIndicator
  split_ifs <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false,
      mul_one, one_mul, mul_zero, zero_mul, mul_assoc]
