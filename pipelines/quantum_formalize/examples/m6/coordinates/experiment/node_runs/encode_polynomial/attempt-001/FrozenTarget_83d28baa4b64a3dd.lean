import M6Coordinates

theorem M6.Coordinates.block_reconstruct : ∀ (N : ℕ) [NeZero N] (p : M6.Cyclic.BinaryPolynomial), p.degree < (N : WithBot ℕ) → M6.Coordinates.blockPolynomial N (M6.Coordinates.coefficients N p) = p := by
  intro N inst p hp
  classical
  change (∑ i : Fin N, Polynomial.C (p.coeff ((i.val : ZMod N).val)) * Polynomial.X ^ i.val) = p
  have hval (i : Fin N) : (i.val : ZMod N).val = i.val := by
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  simp only [hval]
  ext k
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k < N
  · rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin N)]
    · simp
    · intro i hi hne
      have hv : i.val ≠ k := by
        intro h
        apply hne
        exact Fin.ext h
      simp [Polynomial.coeff_C_mul_X_pow, hv, Ne.symm hv]
    · simp
  · have hNk : N ≤ k := Nat.le_of_not_gt hk
    have hdeg : p.degree < (k : WithBot ℕ) := by
      apply lt_of_lt_of_le hp
      exact_mod_cast hNk
    rw [Polynomial.coeff_eq_zero_of_degree_lt hdeg]
    apply Finset.sum_eq_zero
    intro i hi
    have hv : i.val ≠ k := by
      intro h
      exact hk (h ▸ i.isLt)
    simp [Polynomial.coeff_C_mul_X_pow, hv, Ne.symm hv]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (p : M6.Cyclic.BinaryPolynomial), p.degree < (N : WithBot ℕ) → M6.Coordinates.encode N (M6.Coordinates.coefficients N p) = M6.Cyclic.image N p
