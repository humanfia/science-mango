import FrozenTarget_f348582e3b90d9d0
theorem M6.BoundaryFibers.nonzero_monic : QuantumHarnessFrozenTarget := by
  change ∀ p : M6.BoundaryFibers.BP, p ≠ 0 → p.Monic
  intro p hp
  have h : p.leadingCoeff ≠ 0 := by
    simpa only [Polynomial.leadingCoeff_eq_zero] using hp
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  change p.leadingCoeff = 1
  rcases hcases p.leadingCoeff with h0 | h1
  · exact False.elim (h h0)
  · exact h1
