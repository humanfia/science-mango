import FrozenTarget_9709c51dd0113f04
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
    change ((Finset.univ.filter q).card : ℤ) = _
    calc
      ((Finset.univ.filter q).card : ℤ) =
          ∑ a ∈ Finset.univ.filter q, (1 : ℤ) := by simp
      _ = ∑ a : Fin k → Fin T, if q a then (1 : ℤ) else 0 := by
        rw [Finset.sum_filter]
  rw [hR, hc, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  change (∑ a : Fin k → Fin T, ∑ b : Fin k → Fin T,
    (if q a then (1 : ℤ) else 0) * (if q b then (1 : ℤ) else 0)) =
    ∑ a : Fin k → Fin T, ∑ b : Fin k → Fin T,
      if q a ∧ q b then (1 : ℤ) else 0
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hqa : q a <;> by_cases hqb : q b <;> simp [hqa, hqb]
