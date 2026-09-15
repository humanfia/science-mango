import FrozenTarget_8543a04f5f06cab3
theorem M7.QuotientAuto.substitution_bijective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, Function.Bijective (M7.QuotientAuto.substitution u)
  intro N inst u
  constructor
  · intro x y h
    have h' := congrArg (M7.QuotientAuto.substitution (u⁻¹)) h
    simpa only [M7.QuotientAuto.substitution_left_inverse N u] using h'
  · intro y
    exact ⟨M7.QuotientAuto.substitution (u⁻¹) y, M7.QuotientAuto.substitution_right_inverse N u y⟩
