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

theorem M7.ActualFactorized.translate_outer : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.Action.act g c = M7.Action.act (M7.Action.translate g.leftShift g.rightShift) (M7.ActualFactorized.outerImage c (g.unit,g.exchange)) := by
  intro N inst c g
  change M7.Action.act g c = M7.Action.act (M7.Action.translate g.leftShift g.rightShift) (M7.Action.act { unit := g.unit, exchange := g.exchange, leftShift := 0, rightShift := 0 } c)
  rw [← M7.Action.act_compose]
  congr 1
  cases g
  simp [M7.Action.compose, M7.Action.translate]

theorem M7.ActualFactorized.sector_compatibility : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ E : M7.Action.Recipe N → Prop, M7.ActualFactorized.TranslationInvariant E → ∀ g : M7.Action.Record N, E (M7.ActualFactorized.outerImage c (g.unit,g.exchange)) ↔ E (M7.Action.act g c) := by
  intro N inst c E hE g
  rw [M7.ActualFactorized.translate_outer N c g]
  unfold M7.ActualFactorized.TranslationInvariant at hE
  first
  | exact hE _ _ _
  | exact (hE _ _ _).symm
#print axioms M7.ActualFactorized.record_coordinates
#print axioms M7.ActualFactorized.translate_outer
#print axioms M7.ActualFactorized.sector_compatibility
