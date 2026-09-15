import FrozenTarget_1899b0cd4f3a636a
theorem M6.Coordinates.encode_injective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], Function.Injective (M6.Coordinates.encode N)
  intro N inst h k heq
  classical
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N h) =
    AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N k) at heq
  have hdvd : M6.Cyclic.modulus N ∣
      M6.Coordinates.blockPolynomial N h - M6.Coordinates.blockPolynomial N k :=
    AdjoinRoot.mk_eq_mk.mp heq
  obtain ⟨hm, hdeg⟩ := M6.Coordinates.modulus_monic_degree N
  have hlt : (M6.Coordinates.blockPolynomial N h -
      M6.Coordinates.blockPolynomial N k).degree < (M6.Cyclic.modulus N).degree := by
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hdeg]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (M6.Coordinates.block_degree N h) (M6.Coordinates.block_degree N k))
  have hz : M6.Coordinates.blockPolynomial N h -
      M6.Coordinates.blockPolynomial N k = 0 := by
    by_contra hn
    exact (not_lt_of_ge (Polynomial.degree_le_of_dvd hdvd hn)) hlt
  have hp := sub_eq_zero.mp hz
  funext i
  have hc := congrArg (fun p : M6.Cyclic.BinaryPolynomial => p.coeff i.val) hp
  have hi : Fin N := ⟨i.val, ZMod.val_lt i⟩
  have hh := M6.Coordinates.block_coeff N h hi
  have hk := M6.Coordinates.block_coeff N k hi
  change (M6.Coordinates.blockPolynomial N h).coeff i.val = h (i.val : ZMod N) at hh
  change (M6.Coordinates.blockPolynomial N k).coeff i.val = k (i.val : ZMod N) at hk
  rw [hh, hk] at hc
  simpa only [ZMod.natCast_zmod_val] using hc
