import M8MixedNonproduct

theorem M8.MixedNonproduct.product_rectangular : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M8.MixedNonproduct.Product c ↔ ∀ z ∈ M8.MixedNonproduct.Cycles c, ∀ t ∈ M8.MixedNonproduct.Cycles c, (z.1,t.2) ∈ M8.MixedNonproduct.Cycles c := by
  intro N inst c
  unfold M8.MixedNonproduct.Product
  constructor
  · rintro ⟨U, V, h⟩ z hz t ht
    rw [h] at hz ht ⊢
    exact ⟨hz.1, ht.2⟩
  · intro h
    refine ⟨{x | ∃ y, (x, y) ∈ M8.MixedNonproduct.Cycles c},
      {y | ∃ x, (x, y) ∈ M8.MixedNonproduct.Cycles c}, ?_⟩
    apply Set.ext
    intro z
    change z ∈ M8.MixedNonproduct.Cycles c ↔
      (∃ y, (z.1, y) ∈ M8.MixedNonproduct.Cycles c) ∧
      (∃ x, (x, z.2) ∈ M8.MixedNonproduct.Cycles c)
    constructor
    · intro hz
      exact ⟨⟨z.2, hz⟩, ⟨z.1, hz⟩⟩
    · rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
      exact h (z.1, y) hy (x, z.2) hx

theorem M8.MixedNonproduct.word_action : ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), Function.Bijective (M8.MixedNonproduct.wordAction g) ∧ ∀ z : M6.Physical.Word N, M8.MixedNonproduct.wordAction g z ∈ M8.MixedNonproduct.Cycles (M7.Action.act g c) ↔ z ∈ M8.MixedNonproduct.Cycles c := by
  classical
  intro N _ g c
  have hi := M7.Transport.action_isometry N g c
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    first
    | exact Function.LeftInverse.injective (M6.Flatten.flatten_left N)
    | exact Function.LeftInverse.injective (M6.Flatten.flatten_right N)
  have hw : ∀ z : M6.Physical.Word N,
      M6.Flatten.flatten N (M8.MixedNonproduct.wordAction g z) =
        M7.Transport.Xmap g (M6.Flatten.flatten N z) := by
    intro z
    cases he : g.exchange <;>
      simp [M8.MixedNonproduct.wordAction, M7.Transport.Xmap,
        M6.RecipeIsometries.translate, M6.RecipeIsometries.multiplier,
        M6.RecipeIsometries.blockExchange, M6.RecipeIsometries.lift,
        M6.Flatten.flatten_left, M6.Flatten.flatten_right, he]
  constructor
  · have hinj : Function.Injective (M8.MixedNonproduct.wordAction g) := by
      intro x y h
      apply hf
      apply hi.1.1
      rw [← hw x, ← hw y, h]
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩
  · intro z
    have hc := (hi.2 (M6.Flatten.flatten N z)).2.1
    rw [← hw z] at hc
    simpa [M7.Transport.CX, M8.MixedNonproduct.Cycles,
      M6.Spaces.cycle_words_iff, M6.Flatten.flatten_left,
      M6.Flatten.flatten_right] using hc
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M8.MixedNonproduct.Product (M7.Action.act g c) ↔ M8.MixedNonproduct.Product c
