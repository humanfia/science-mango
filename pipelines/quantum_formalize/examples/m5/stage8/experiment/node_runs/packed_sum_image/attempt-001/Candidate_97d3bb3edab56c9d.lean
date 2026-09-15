import FrozenTarget_97d3bb3edab56c9d
theorem M5.SupportPolynomial.packed_sum_image : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r) → M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r) = ∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ M5.Packing.packedValue r i
  intro w T r hinj
  classical
  unfold M5.SupportPolynomial.ofSupport M5.Packing.packedSupport
  apply Finset.sum_image
  intro i hi j hj hij
  exact hinj hij
