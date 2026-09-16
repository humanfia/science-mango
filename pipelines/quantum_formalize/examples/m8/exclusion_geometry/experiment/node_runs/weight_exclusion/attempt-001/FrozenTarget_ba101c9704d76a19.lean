import M8ExclusionGeometry

theorem M8.ExclusionGeometry.card_sup : ∀ (N : ℕ) [NeZero N], ∀ B : Finset (ZMod N), B.card ≤ B.sup ZMod.val + 1 := by
  change ∀ (N : ℕ) [NeZero N], ∀ B : Finset (ZMod N), B.card ≤ B.sup ZMod.val + 1
  intro N inst B
  classical
  have hinj : Function.Injective (ZMod.val : ZMod N → ℕ) := by
    intro a b h
    have hc := congrArg (fun k : ℕ => (k : ZMod N)) h
    simpa using hc
  have hsub : B.image ZMod.val ⊆ Finset.range (B.sup ZMod.val + 1) := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup hx)
  calc
    B.card = (B.image ZMod.val).card := (Finset.card_image_of_injective B hinj).symm
    _ ≤ (Finset.range (B.sup ZMod.val + 1)).card := Finset.card_le_card hsub
    _ = B.sup ZMod.val + 1 := Finset.card_range _

theorem M8.ExclusionGeometry.weight_orbit_span : ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), c.1.card = w → c.2.card = w → w ≤ M8.Anchor.span (M7.Action.act g c) + 1 := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (w L : ℕ) (c : M7.Action.Recipe N), c.1.card = w → c.2.card = w → L+1 < w → ∀ g : M7.Action.Record N, L < M8.Anchor.span (M7.Action.act g c)
