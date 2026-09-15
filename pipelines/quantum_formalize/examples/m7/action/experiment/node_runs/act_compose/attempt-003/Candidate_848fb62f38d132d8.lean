import FrozenTarget_848fb62f38d132d8
theorem M7.Action.act_compose : QuantumHarnessFrozenTarget := by
  intro N inst g h c
  classical
  have ha (u v : (ZMod N)ˣ) (a s : ZMod N) :
      M7.Action.affine (u * v) ((u : ZMod N) * a + s) =
        fun x => M7.Action.affine u s (M7.Action.affine v a x) := by
    funext x
    simp only [M7.Action.affine, Units.val_mul]
    ring
  rcases g with ⟨u, e, s, t⟩
  rcases h with ⟨v, f, a, b⟩
  cases e <;> cases f <;>
    simp [M7.Action.act, M7.Action.compose, ha, Finset.image_image, Function.comp_def]
