import FrozenTarget_1d098fb026b0f52f
theorem M5.ResidueCount.two_block_R_count : QuantumHarnessFrozenTarget := by
  classical
  intro P T d k hP hT hd
  have hR : M5.ResidueCount.ROne P T d k =
      (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ) := by
    simpa only [M5.ResidueCount.ROne, dif_pos hP] using
      M5.AnchoredTupleCount.restricted_R_count P hP T d k hT hd
  let q : (Fin k → Fin T) → Prop := fun a =>
    (∀ i, d ∣ (a i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial a
  have hc : (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ) =
      ∑ a : Fin k → Fin T, if q a then (1 : ℤ) else 0 := by
    change ((Finset.univ.filter q).card : ℤ) =
      ∑ a : Fin k → Fin T, if q a then (1 : ℤ) else 0
    simp [← Finset.sum_filter]
  change M5.ResidueCount.ROne P T d k ^ 2 =
    ∑ a : Fin k → Fin T, ∑ b : Fin k → Fin T,
      if q a ∧ q b then (1 : ℤ) else 0
  rw [hR, hc, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hqa : q a <;> by_cases hqb : q b <;> simp [hqa, hqb]
