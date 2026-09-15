import FrozenTarget_fc895e71368ebb74
theorem M5.PhysicalOrder.period_control : QuantumHarnessFrozenTarget := by
  intro A B w T hw hT hA hB hBbound
  have hAc : (M5.SupportPolynomial.ofSupport A).coeff 0 = 1 := by
    apply M5.SupportPolynomial.support_coeff_zero
    exact hA
  have hBc : (M5.SupportPolynomial.ofSupport B).coeff 0 = 1 := by
    apply M5.SupportPolynomial.support_coeff_zero
    exact hB
  have hwT : 0 < w * T := Nat.mul_pos (by omega) hT
  have hdeg : (M5.SupportPolynomial.ofSupport B).natDegree < w * T := by
    apply M5.SupportPolynomial.support_degree_bound <;> assumption
  unfold M5.PhysicalOrder.supportPeriod
  constructor
  · solve_by_elim (maxDepth := 12) [M5.Signature.ordinary_gcd_properties, M5.Signature.ordinary_gcd_period_bound, M5.Period.period_law, And.left, And.right]
  · constructor
    · calc
        _ ≤ 2 ^ (M5.SupportPolynomial.ofSupport B).natDegree := by
          solve_by_elim (maxDepth := 12) [M5.Signature.ordinary_gcd_period_bound, M5.Signature.ordinary_gcd_properties, And.left, And.right]
        _ ≤ 2 ^ (w * T) := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hdeg)
    · solve_by_elim (maxDepth := 14) [M5.Signature.ordinary_gcd_properties, M5.Period.period_law, And.left, And.right, Iff.mpr, dvd_refl]
