import FrozenTarget_1f0adec311003a49
theorem M8.P3Family.nontrivial : QuantumHarnessFrozenTarget := by
  change M8.P3Family.polynomial ≠ 1 ∧ M8.P3Family.polynomial ≠ 0 ∧ M8.P3Family.polynomial.natDegree = 2
  have hc : M8.P3Family.polynomial.coeff 2 ≠ 0 := by
    norm_num [M8.P3Family.polynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow]
  have hd : M8.P3Family.polynomial.natDegree = 2 := by
    apply le_antisymm
    · unfold M8.P3Family.polynomial
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (Polynomial.natDegree_add_le _ _) ?_
        norm_num
      · simp
    · exact Polynomial.le_natDegree_of_ne_zero hc
  refine ⟨?_, ?_, hd⟩
  · intro h
    rw [h] at hd
    norm_num at hd
  · intro h
    rw [h] at hd
    norm_num at hd
