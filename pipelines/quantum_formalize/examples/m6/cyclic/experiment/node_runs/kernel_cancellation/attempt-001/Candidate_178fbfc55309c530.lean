import FrozenTarget_178fbfc55309c530
theorem M6.Cyclic.kernel_cancellation : QuantumHarnessFrozenTarget := by
  change ∀ F K h : M6.Cyclic.BinaryPolynomial, F ≠ 0 → (F * K ∣ F * h ↔ K ∣ h)
  intro F K h hF
  exact mul_dvd_mul_iff_left hF
