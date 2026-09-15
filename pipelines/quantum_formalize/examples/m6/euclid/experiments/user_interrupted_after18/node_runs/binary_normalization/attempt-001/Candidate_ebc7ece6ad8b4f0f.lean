import FrozenTarget_ebc7ece6ad8b4f0f
theorem M6.Euclid.binary_normalization : QuantumHarnessFrozenTarget := by
  change ∀ p : M6.Euclid.BP, (p ≠ 0 → p.Monic) ∧ normalize p = p
  intro p
  have hm : p ≠ 0 → p.Monic := by
    intro hp
    change p.leadingCoeff = 1
    have binary : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases binary p.leadingCoeff with h | h
    · exact False.elim (hp (Polynomial.leadingCoeff_eq_zero.mp h))
    · exact h
  refine ⟨hm, ?_⟩
  by_cases hp : p = 0
  · subst p
    simp
  · exact (hm hp).normalize_eq_self
