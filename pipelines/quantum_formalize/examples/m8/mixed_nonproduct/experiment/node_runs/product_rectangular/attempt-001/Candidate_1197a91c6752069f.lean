import FrozenTarget_1197a91c6752069f
theorem M8.MixedNonproduct.product_rectangular : QuantumHarnessFrozenTarget := by
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
