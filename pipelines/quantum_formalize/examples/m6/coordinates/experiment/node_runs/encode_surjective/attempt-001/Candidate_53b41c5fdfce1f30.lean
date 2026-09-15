import FrozenTarget_53b41c5fdfce1f30
theorem M6.Coordinates.encode_surjective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], Function.Surjective (M6.Coordinates.encode N)
  intro N inst y
  classical
  refine AdjoinRoot.induction_on _ y ?_
  intro p
  obtain ⟨hm, hn⟩ := M6.Coordinates.modulus_monic_degree N
  have hd : (M6.Cyclic.modulus N).degree = (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hn]
  have hr : (p %ₘ M6.Cyclic.modulus N).degree < (N : WithBot ℕ) := by
    rw [← hd]
    exact Polynomial.degree_modByMonic_lt p hm
  refine ⟨M6.Coordinates.coefficients N (p %ₘ M6.Cyclic.modulus N), ?_⟩
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N (M6.Coordinates.coefficients N (p %ₘ M6.Cyclic.modulus N))) = AdjoinRoot.mk (M6.Cyclic.modulus N) p
  rw [M6.Coordinates.block_reconstruct N _ hr]
  symm
  apply AdjoinRoot.mk_eq_mk.mpr
  rw [Polynomial.modByMonic_eq_sub_mul_div, sub_sub_cancel]
  exact dvd_mul_right _ _
