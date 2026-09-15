import M7ActualFactorizedReady

theorem M7.ActualFactorized.translate_outer : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.Action.act g c = M7.Action.act (M7.Action.translate g.leftShift g.rightShift) (M7.ActualFactorized.outerImage c (g.unit,g.exchange)) := by
  intro N inst c g
  change M7.Action.act g c = M7.Action.act (M7.Action.translate g.leftShift g.rightShift) (M7.Action.act { unit := g.unit, exchange := g.exchange, leftShift := 0, rightShift := 0 } c)
  rw [← M7.Action.act_compose]
  congr 1
  cases g
  simp [M7.Action.compose, M7.Action.translate]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ E : M7.Action.Recipe N → Prop, M7.ActualFactorized.TranslationInvariant E → ∀ g : M7.Action.Record N, E (M7.ActualFactorized.outerImage c (g.unit,g.exchange)) ↔ E (M7.Action.act g c)
