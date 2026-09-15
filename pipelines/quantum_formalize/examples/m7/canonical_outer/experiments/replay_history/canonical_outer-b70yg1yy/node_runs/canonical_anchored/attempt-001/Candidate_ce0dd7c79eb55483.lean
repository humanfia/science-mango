import FrozenTarget_ce0dd7c79eb55483
theorem M7.CanonicalOuter.canonical_anchored : QuantumHarnessFrozenTarget := by
  intro N inst c h₁ h₂
  classical
  let g := M7.CanonicalOuter.outerRecord (M7.CanonicalOuter.chosenOuter c)
  change 0 ∈ M7.CanonicalBlock.normalize (M7.Action.act g c).1 ∧
    0 ∈ M7.CanonicalBlock.normalize (M7.Action.act g c).2
  have hleft : 0 < c.1.card := Finset.card_pos.mpr h₁
  have hright : 0 < c.2.card := Finset.card_pos.mpr h₂
  have hc := M7.Action.support_cards N g c
  constructor
  · apply M7.CanonicalBlock.normalize_anchor N
    apply Finset.card_pos.mp
    rw [hc.1]
    split <;> assumption
  · apply M7.CanonicalBlock.normalize_anchor N
    apply Finset.card_pos.mp
    rw [hc.2]
    split <;> assumption
