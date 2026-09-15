import FrozenTarget_65c8511ed114cb76
theorem M7.SignatureIdeal.principal_gcd : QuantumHarnessFrozenTarget := by
  intro N inst F
  let f : M6.Cyclic.BinaryPolynomial →+* M6.Cyclic.CycleRing N := AdjoinRoot.mk (M6.Cyclic.modulus N)
  change Ideal.span ({f F} : Set (M6.Cyclic.CycleRing N)) = Ideal.span ({f (EuclideanDomain.gcd F (M6.Cyclic.modulus N))} : Set (M6.Cyclic.CycleRing N))
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    rcases EuclideanDomain.gcd_dvd_left F (M6.Cyclic.modulus N) with ⟨u, hu⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨f u, ?_⟩
    exact (congrArg f hu).trans (map_mul f _ _)
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    have hz : f (M6.Cyclic.modulus N) = 0 := AdjoinRoot.mk_self
    have he := congrArg f (EuclideanDomain.gcd_eq_gcd_ab F (M6.Cyclic.modulus N))
    simp only [map_add, map_mul, hz, zero_mul, mul_zero, add_zero, zero_add] at he
    rw [he]
    first
    | apply Ideal.mul_mem_left
      exact Ideal.subset_span (by simp)
    | rw [mul_comm]
      apply Ideal.mul_mem_left
      exact Ideal.subset_span (by simp)
