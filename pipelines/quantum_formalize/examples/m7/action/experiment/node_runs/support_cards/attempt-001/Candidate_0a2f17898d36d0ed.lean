import FrozenTarget_0a2f17898d36d0ed
theorem M7.Action.support_cards : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Action.Recipe N), (M7.Action.act g c).1.card = (if g.exchange then c.2.card else c.1.card) ∧ (M7.Action.act g c).2.card = (if g.exchange then c.1.card else c.2.card)
  intro N inst g c
  classical
  dsimp only [M7.Action.act]
  rw [Finset.card_image_of_injective _ (M7.Action.affine_bijective N g.unit g.leftShift).injective,
      Finset.card_image_of_injective _ (M7.Action.affine_bijective N g.unit g.rightShift).injective]
  cases g.exchange <;> simp
