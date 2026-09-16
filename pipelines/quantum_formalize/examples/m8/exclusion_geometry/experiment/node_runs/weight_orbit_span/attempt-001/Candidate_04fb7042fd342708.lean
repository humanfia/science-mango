import FrozenTarget_04fb7042fd342708
theorem M8.ExclusionGeometry.weight_orbit_span : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), c.1.card = w → c.2.card = w → w ≤ M8.Anchor.span (M7.Action.act g c) + 1
  intro N inst w c g h₁ h₂
  classical
  have hc : (M7.Action.act g c).1.card = w := by
    simpa [h₁, h₂] using (M7.Action.support_cards N g c).1
  have hs : (M7.Action.act g c).1.sup ZMod.val ≤ M8.Anchor.span (M7.Action.act g c) := by
    apply Finset.sup_le
    intro i hi
    exact ((M8.Anchor.span_le N (M7.Action.act g c) (M8.Anchor.span (M7.Action.act g c))).mp le_rfl).1 i hi
  calc
    w = (M7.Action.act g c).1.card := hc.symm
    _ ≤ (M7.Action.act g c).1.sup ZMod.val + 1 := M8.ExclusionGeometry.card_sup N _
    _ ≤ M8.Anchor.span (M7.Action.act g c) + 1 := Nat.add_le_add_right hs 1
