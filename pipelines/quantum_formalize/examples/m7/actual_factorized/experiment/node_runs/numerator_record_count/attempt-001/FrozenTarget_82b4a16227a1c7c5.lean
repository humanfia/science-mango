import M7ActualFactorizedReady

theorem M7.ActualFactorized.record_coordinates : ∀ (N : ℕ) [NeZero N], Function.Bijective (@M7.ActualFactorized.toRecord N _) := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ (sector : M7.ActualFactorized.Outer N → Prop) (L R : Finset (ZMod N) → Prop), M7.ActualFactorized.numerator c sector L R = M7.ActualFactorized.recordCount c sector L R
