import FrozenTarget_82f3d32b2ec15587
theorem M6.Pinned.enumerator_zero_coeff : QuantumHarnessFrozenTarget := by
  classical
  intro m L P hzero
  rw [M6.Pinned.enumerator_coeff]
  obtain ⟨hnonneg, hpos⟩ := M6.Pinned.count_nonnegative_positive m L P 0
  apply le_antisymm _ hnonneg
  apply le_of_not_gt
  intro h
  obtain ⟨v, hvL, _, hw⟩ := hpos.mp h
  have hvzero : v = 0 := by
    funext i
    change v i = 0
    by_contra hi
    unfold M6.Pinned.weight at hw
    have hempty := Finset.card_eq_zero.mp hw
    have hmem : i ∈ Finset.univ.filter (fun j : Fin m => v j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    rw [hempty] at hmem
    simpa using hmem
  exact hzero (hvzero ▸ hvL)
