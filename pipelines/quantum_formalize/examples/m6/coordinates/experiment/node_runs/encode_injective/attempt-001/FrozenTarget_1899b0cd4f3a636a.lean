import M6Coordinates

theorem M6.Coordinates.block_coeff : ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N) (i : Fin N), (M6.Coordinates.blockPolynomial N h).coeff i.val = h (i.val : ZMod N) := by
  intro N inst h i
  classical
  simp [M6.Coordinates.blockPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Fin.val_eq_val, i.isLt]

theorem M6.Coordinates.block_degree : ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N), (M6.Coordinates.blockPolynomial N h).degree < (N : WithBot ℕ) := by
  intro N _ h
  classical
  unfold M6.Coordinates.blockPolynomial
  simp only [Polynomial.C_mul_X_pow_eq_monomial]
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  apply (Finset.sup_lt_iff (by simp)).2
  intro i hi
  apply lt_of_le_of_lt (Polynomial.degree_monomial_le _ _)
  first
  | exact_mod_cast i.isLt
  | exact_mod_cast ZMod.val_lt i
  | exact_mod_cast Finset.mem_range.mp hi

theorem M6.Coordinates.modulus_monic_degree : ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic ∧ (M6.Cyclic.modulus N).natDegree = N := by
  change ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic ∧ (M6.Cyclic.modulus N).natDegree = N
  intro N inst
  change (Polynomial.X ^ N + (1 : Polynomial (ZMod 2))).Monic ∧ (Polynomial.X ^ N + (1 : Polynomial (ZMod 2))).natDegree = N
  constructor
  · simpa only [Polynomial.C_1] using (Polynomial.monic_X_pow_add_C (1 : ZMod 2) (NeZero.ne N))
  · simpa only [Polynomial.C_1] using (Polynomial.natDegree_X_pow_add_C (n := N) (r := (1 : ZMod 2)))
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], Function.Injective (M6.Coordinates.encode N)
