import FrozenTarget_fd779317299d5e91
theorem M7.ActualFactorized.record_coordinates : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], Function.Bijective (@M7.ActualFactorized.toRecord N _)
  intro N inst
  have hleft : Function.LeftInverse (@M7.ActualFactorized.fromRecord N _) (@M7.ActualFactorized.toRecord N _) := by
    rintro ⟨⟨u, e⟩, s, t⟩
    rfl
  have hright : Function.RightInverse (@M7.ActualFactorized.fromRecord N _) (@M7.ActualFactorized.toRecord N _) := by
    intro g
    cases g
    rfl
  exact ⟨hleft.injective, hright.surjective⟩
