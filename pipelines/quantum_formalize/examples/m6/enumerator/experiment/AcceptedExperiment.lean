import M6Enumerator

theorem M6.Pinned.enumerator_sdiff : ∀ (m : ℕ) (B C : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), B ⊆ C → M6.Pinned.enumerator (C \ B) P = M6.Pinned.enumerator C P - M6.Pinned.enumerator B P := by
  intro m B C P hBC
  classical
  unfold M6.Pinned.enumerator
  apply eq_sub_iff_add_eq.mpr
  exact Finset.sum_sdiff hBC

theorem M6.Pinned.enumerator_total : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), Polynomial.eval 1 (M6.Pinned.enumerator L (M6.Pinned.free m)) = (L.card : ℤ) := by
  classical
  intro m L
  change (Polynomial.evalRingHom (1 : ℤ)) (M6.Pinned.enumerator L (M6.Pinned.free m)) = (L.card : ℤ)
  simp [M6.Pinned.enumerator, M6.Pinned.agrees, M6.Pinned.free]

theorem M6.Pinned.enumerator_zero_coeff : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), (0 : M6.Pinned.Vector m) ∉ L → (M6.Pinned.enumerator L P).coeff 0 = 0 := by
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
#print axioms M6.Pinned.enumerator_sdiff
#print axioms M6.Pinned.enumerator_total
#print axioms M6.Pinned.enumerator_zero_coeff
