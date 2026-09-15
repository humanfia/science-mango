import FrozenTarget_e47ceaa847cb1afa
theorem M6.BoundaryFibers.nonzero_monic : QuantumHarnessFrozenTarget := by
  change ∀ p : M6.BoundaryFibers.BP, p ≠ 0 → p.Monic
  intro p hp
  have hlc : p.leadingCoeff ≠ 0 := by
    intro h
    exact hp (Polynomial.leadingCoeff_eq_zero.mp h)
  change p.leadingCoeff = 1
  have hbinary : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact hbinary p.leadingCoeff hlc
