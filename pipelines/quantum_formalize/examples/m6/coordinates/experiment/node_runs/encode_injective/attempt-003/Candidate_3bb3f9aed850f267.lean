import FrozenTarget_3bb3f9aed850f267
theorem M6.Coordinates.encode_injective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], Function.Injective (M6.Coordinates.encode N)
  intro N inst h k heq
  classical
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N h) = AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Coordinates.blockPolynomial N k) at heq
  have hdiv := AdjoinRoot.mk_eq_mk.mp heq
  obtain ⟨hm, hnat⟩ := M6.Coordinates.modulus_monic_degree N
  have hmdeg : (M6.Cyclic.modulus N).degree = (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hnat]
  have hlt : (M6.Coordinates.blockPolynomial N h - M6.Coordinates.blockPolynomial N k).degree < (M6.Cyclic.modulus N).degree := by
    rw [hmdeg]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (M6.Coordinates.block_degree N h) (M6.Coordinates.block_degree N k))
  have hz : M6.Coordinates.blockPolynomial N h - M6.Coordinates.blockPolynomial N k = 0 := by
    by_contra hn
    have hle : (M6.Cyclic.modulus N).degree ≤ (M6.Coordinates.blockPolynomial N h - M6.Coordinates.blockPolynomial N k).degree := by
      first
      | exact Polynomial.degree_le_of_dvd hdiv hn
      | exact Polynomial.degree_le_of_dvd hn hdiv
    exact (not_lt_of_ge hle) hlt
  have hp := sub_eq_zero.mp hz
  funext i
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff i.val) hp
  rw [M6.Coordinates.block_coeff N h ⟨i.val, ZMod.val_lt i⟩, M6.Coordinates.block_coeff N k ⟨i.val, ZMod.val_lt i⟩] at hc
  simpa using hc
