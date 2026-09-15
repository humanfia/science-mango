import FrozenTarget_fa8fa3afeaee101b
theorem M5.ResidueCount.two_block_R_count : QuantumHarnessFrozenTarget := by
  classical
  intro P T d k hP hT hd
  have hR : M5.ResidueCount.ROne P T d k =
      (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ) := by
    simpa only [M5.ResidueCount.ROne, dif_pos hP] using
      (M5.AnchoredTupleCount.restricted_R_count P hP T d k hT hd)
  have hcount : (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ) =
      ∑ a : Fin k → Fin T,
        if (∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial a
        then (1 : ℤ) else 0 := by
    simp [M5.AnchoredTupleCount.restrictedCount,
      M5.ResidueCount.tailPolynomial, ← Finset.sum_filter]
  rw [hR, hcount, pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases ha' : (∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial a <;>
    by_cases hb' : (∀ i : Fin k, d ∣ (b i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial b <;>
    simp [ha', hb']
