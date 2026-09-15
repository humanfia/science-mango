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

theorem M7.ActualFactorized.numerator_record_count : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ (sector : M7.ActualFactorized.Outer N → Prop) (L R : Finset (ZMod N) → Prop), M7.ActualFactorized.numerator c sector L R = M7.ActualFactorized.recordCount c sector L R := by
  intro N inst c sector L R
  classical
  unfold M7.ActualFactorized.numerator M7.ActualFactorized.recordCount
  rw [M7.Factorized.numerator_record_card]
  refine Finset.card_bij (fun a _ => M7.ActualFactorized.toRecord a) ?_ ?_ ?_
  · rintro ⟨⟨u, e⟩, s, t⟩ ha
    simp only [M7.Factorized.records, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a ha b hb hab
    exact (M7.ActualFactorized.record_coordinates N).1 hab
  · intro g hg
    refine ⟨M7.ActualFactorized.fromRecord g, ?_, ?_⟩
    · simp only [M7.Factorized.records, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact hg
    · cases g
      rfl

theorem M7.ActualFactorized.sector_compatibility : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ E : M7.Action.Recipe N → Prop, M7.ActualFactorized.TranslationInvariant E → ∀ g : M7.Action.Record N, E (M7.ActualFactorized.outerImage c (g.unit,g.exchange)) ↔ E (M7.Action.act g c) := by
  intro N inst c E hE g
  rw [M7.ActualFactorized.translate_outer N c g]
  unfold M7.ActualFactorized.TranslationInvariant at hE
  first
  | exact hE _ _ _
  | exact (hE _ _ _).symm
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ (E : M7.Action.Recipe N → Prop) (L R : Finset (ZMod N) → Prop), M7.ActualFactorized.TranslationInvariant E → M7.ActualFactorized.numerator c (fun u => E (M7.ActualFactorized.outerImage c u)) L R = M7.ActualOrbit.actionCount c (fun y => E y ∧ L y.1 ∧ R y.2)
