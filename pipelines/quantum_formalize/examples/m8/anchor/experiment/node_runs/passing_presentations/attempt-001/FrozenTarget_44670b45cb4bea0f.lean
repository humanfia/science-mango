import M8Anchor

theorem M8.Anchor.anchored : ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b → M8.Anchor.Anchored (M8.Anchor.trial c e u a b) := by
  intro N _ c e u a b h
  cases e <;> simp only [M8.Anchor.Eligible, M8.Anchor.left, M8.Anchor.right, Bool.false_eq_true, if_false, if_true] at h
  all_goals
    rcases h with ⟨ha, hb⟩
    dsimp [M8.Anchor.Anchored, M8.Anchor.trial, M8.Anchor.record, M7.Action.act]
    constructor
  all_goals
    first
    | exact Finset.mem_image.mpr ⟨a, ha, by simp [M7.Action.affine]⟩
    | exact Finset.mem_image.mpr ⟨b, hb, by simp [M7.Action.affine]⟩

theorem M8.Anchor.translation_reconstruction : ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (g : M7.Action.Record N), M8.Anchor.Anchored (M7.Action.act g c) → ∃ a b : ZMod N, M8.Anchor.Eligible c g.exchange a b ∧ M8.Anchor.record g.exchange g.unit a b = g := by
  intro N inst c g h
  classical
  rcases g with ⟨u, e, s, t⟩
  cases e <;> simp [M8.Anchor.Anchored, M7.Action.act, M7.Action.affine, Finset.mem_image] at h
  all_goals
    rcases h with ⟨⟨a, ha, hsa⟩, ⟨b, hb, htb⟩⟩
    have hs : -((u : ZMod N) * a) = s := by
      linear_combination -hsa
    have ht : -((u : ZMod N) * b) = t := by
      linear_combination -htb
    refine ⟨a, b, ?_, ?_⟩
    · exact ⟨ha, hb⟩
    · simp [M8.Anchor.record, hs, ht]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (L : ℕ), (∃ (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b ∧ M8.Anchor.span (M8.Anchor.trial c e u a b) ≤ L) ↔ ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) ≤ L
