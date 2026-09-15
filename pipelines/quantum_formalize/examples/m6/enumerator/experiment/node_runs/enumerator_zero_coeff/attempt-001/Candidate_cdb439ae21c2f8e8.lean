import FrozenTarget_cdb439ae21c2f8e8
theorem M6.Pinned.enumerator_zero_coeff : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), (0 : M6.Pinned.Vector m) ∉ L → (M6.Pinned.enumerator L P).coeff 0 = 0
  intro m L P hzero
  rw [M6.Pinned.enumerator_coeff m L P 0]
  obtain ⟨hnonneg, hpos⟩ := M6.Pinned.count_nonnegative_positive m L P 0
  apply le_antisymm _ hnonneg
  by_contra h
  obtain ⟨v, hv, _, hw⟩ := hpos.mp (lt_of_not_ge h)
  have hvzero : v = 0 := by
    unfold M6.Pinned.weight at hw
    funext i
    have hi := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hw) i (Finset.mem_univ i)
    simpa using hi
  exact hzero (hvzero ▸ hv)
