import FrozenTarget_37919e38a08469c7
theorem M7.SignatureIdeal.full_signature_ideal : QuantumHarnessFrozenTarget := by
  intro N inst a b
  let f : M6.Cyclic.BinaryPolynomial →+* M6.Cyclic.CycleRing N := AdjoinRoot.mk (M6.Cyclic.modulus N)
  change Ideal.span ({f a, f b} : Set (M6.Cyclic.CycleRing N)) = Ideal.span ({f (M6.Cyclic.signature a b (M6.Cyclic.modulus N))} : Set (M6.Cyclic.CycleRing N))
  rcases M6.Cyclic.signature_divides a b (M6.Cyclic.modulus N) with ⟨ha, hb, hm⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rcases ha with ⟨u, hu⟩
      apply Ideal.mem_span_singleton.mpr
      exact ⟨f u, by rw [hu, map_mul]⟩
    · rcases hb with ⟨u, hu⟩
      apply Ideal.mem_span_singleton.mpr
      exact ⟨f u, by rw [hu, map_mul]⟩
  · apply Ideal.span_le.mpr
    intro x hx
    have hx' := Set.mem_singleton_iff.mp hx
    subst x
    have ha' : f a ∈ Ideal.span ({f a, f b} : Set (M6.Cyclic.CycleRing N)) := Ideal.subset_span (by simp)
    have hb' : f b ∈ Ideal.span ({f a, f b} : Set (M6.Cyclic.CycleRing N)) := Ideal.subset_span (by simp)
    rcases M6.Cyclic.signature_bezout a b (M6.Cyclic.modulus N) with ⟨p, q, r, h⟩
    have hz : f (M6.Cyclic.modulus N) = 0 := AdjoinRoot.mk_self
    have he := congrArg f h
    simp only [map_add, map_mul, hz, mul_zero, add_zero] at he
    rw [he]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha') (Ideal.mul_mem_left _ _ hb')
