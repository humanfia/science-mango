import FrozenTarget_e5bf8bc2d3cea19a
theorem M5.ResidueCount.pair_indicator_exact : QuantumHarnessFrozenTarget := by
  classical
  intro T k F a b hT hF hFT
  have hc := M5.Connectivity.connected_indicator T
    (M5.ResidueCount.residueSupport a)
    (M5.ResidueCount.residueSupport b) hT
  have hp := M5.PolynomialIndicator.exact_signature_indicator
    (M5.ResidueCount.tailPolynomial a)
    (M5.ResidueCount.tailPolynomial b) F T hT hF hFT
  simp [M5.ResidueCount.residueSupport, M5.Connectivity.supportGcd,
    Finset.gcd_image, Function.comp_def] at hc
  unfold M5.ResidueCount.pairIndicator M5.ResidueCount.feasible
  simp only [hp]
  simp_all [M5.ResidueCount.residueSupport, M5.Connectivity.supportGcd,
    Finset.gcd_image, Function.comp_def, ← Finset.sum_mul, ← Finset.mul_sum,
    ite_mul, mul_ite, and_assoc, and_comm, and_left_comm]
  <;> split_ifs at * <;> simp_all
