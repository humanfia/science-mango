import FrozenTarget_45bcb11188a13cbc
theorem M6.Coordinates.encode_injective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], Function.Injective (M6.Coordinates.encode N)
  intro N inst h k heq
  classical
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N h) =
    AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N k) at heq
  have hdvd := (AdjoinRoot.mk_eq_mk (M6.Cyclic.modulus N)).mp heq
  have hlt : (M6.Coordinates.blockPolynomial N h - M6.Coordinates.blockPolynomial N k).degree < (N : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (M6.Coordinates.block_degree N h) (M6.Coordinates.block_degree N k))
  have hz : M6.Coordinates.blockPolynomial N h - M6.Coordinates.blockPolynomial N k = 0 := by
    by_contra hn
    have hle := Polynomial.degree_le_of_dvd hdvd hn
    have hm := M6.Coordinates.modulus_monic_degree N
    rw [Polynomial.degree_eq_natDegree hm.1.ne_zero, hm.2] at hle
    exact (not_lt_of_ge hle) hlt
  have hp := sub_eq_zero.mp hz
  funext x
  let i : Fin N := ⟨x.val, ZMod.val_lt x⟩
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff i.val) hp
  rw [M6.Coordinates.block_coeff N h i, M6.Coordinates.block_coeff N k i] at hc
  simpa only [i, ZMod.natCast_zmod_val] using hc
