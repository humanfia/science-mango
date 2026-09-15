import FrozenTarget_a51063b895433c99
theorem M5.SupportPolynomial.packed_polynomial_residue : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r)) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofResidueTuple r)
  intro w T r
  classical
  rw [M5.SupportPolynomial.packed_sum_image w T r (by apply M5.Packing.packed_value_injective)]
  unfold M5.SupportPolynomial.ofResidueTuple
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold M5.Packing.packedValue
  apply M5.SupportPolynomial.quotient_monomial_period
