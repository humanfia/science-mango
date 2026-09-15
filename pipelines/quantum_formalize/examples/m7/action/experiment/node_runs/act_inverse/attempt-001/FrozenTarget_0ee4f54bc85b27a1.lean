import M7Action

theorem M7.Action.act_compose : ∀ (N : ℕ) [NeZero N], ∀ (g h : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.compose g h) c = M7.Action.act g (M7.Action.act h c) := by
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

theorem M7.Action.act_identity : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.Action.identity N) c = c := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.Action.identity N) c = c
  intro N inst c
  have h : M7.Action.affine (1 : (ZMod N)ˣ) (0 : ZMod N) = id := by
    funext i
    simp [M7.Action.affine]
  rcases c with ⟨s, t⟩
  simp [M7.Action.act, M7.Action.identity, h]

theorem M7.Action.left_inverse : ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.inverse g) g = M7.Action.identity N := by
  change ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.inverse g) g = M7.Action.identity N
  intro N inst g
  rcases g with ⟨u, e, s, t⟩
  cases e <;> simp [M7.Action.compose, M7.Action.inverse, M7.Action.identity]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.inverse g) (M7.Action.act g c) = c
