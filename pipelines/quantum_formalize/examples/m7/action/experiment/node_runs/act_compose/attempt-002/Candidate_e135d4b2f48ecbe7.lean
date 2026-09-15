import FrozenTarget_e135d4b2f48ecbe7
theorem M7.Action.act_compose : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (g h : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.compose g h) c = M7.Action.act g (M7.Action.act h c)
  intro N _ g h c
  classical
  have ha (u v : (ZMod N)ˣ) (a s : ZMod N) :
      M7.Action.affine (u * v) ((u : ZMod N) * a + s) =
        (fun x => M7.Action.affine u s (M7.Action.affine v a x)) := by
    funext x
    simp [M7.Action.affine, mul_add, mul_assoc, add_assoc]
  rcases g with ⟨u, e, s, t⟩
  rcases h with ⟨v, f, a, b⟩
  cases e <;> cases f <;>
    simp [M7.Action.act, M7.Action.compose, Finset.image_image, ha]
