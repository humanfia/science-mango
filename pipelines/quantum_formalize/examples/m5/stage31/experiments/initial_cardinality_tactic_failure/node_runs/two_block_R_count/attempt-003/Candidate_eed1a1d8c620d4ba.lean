import FrozenTarget_eed1a1d8c620d4ba
theorem M5.ResidueCount.two_block_R_count : QuantumHarnessFrozenTarget := by
  classical
  intro P T d k hP hT hd
  have hR : M5.ResidueCount.ROne P T d k =
      (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ) := by
    simpa only [M5.ResidueCount.ROne, dif_pos hP] using
      M5.AnchoredTupleCount.restricted_R_count P hP T d k hT hd
  let q : (Fin k → Fin T) → Prop := fun a =>
    (∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial a
  have hc : (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ) =
      ∑ a : Fin k → Fin T, if q a then (1 : ℤ) else 0 := by
    rw [← Finset.sum_filter]
    simp [M5.AnchoredTupleCount.restrictedCount, q,
      M5.ResidueCount.tailPolynomial]
  rw [hR, hc, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha_mem
  apply Finset.sum_congr rfl
  intro b hb_mem
  by_cases ha : q a <;> by_cases hb : q b
  all_goals
    dsimp only [q] at ha hb ⊢
    simp [ha, hb]
