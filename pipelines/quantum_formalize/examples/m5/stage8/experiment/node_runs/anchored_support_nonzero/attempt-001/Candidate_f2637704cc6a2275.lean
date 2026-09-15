import FrozenTarget_f2637704cc6a2275
theorem M5.SupportPolynomial.anchored_support_nonzero : QuantumHarnessFrozenTarget := by
  change ∀ S : Finset ℕ, 0 ∈ S → M5.SupportPolynomial.ofSupport S ≠ 0
  intro S hS hzero
  have hcoeff := M5.SupportPolynomial.support_coeff_zero S
  simpa [hzero, hS] using hcoeff
