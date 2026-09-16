import M7SignatureIdeal

theorem M7.SignatureIdeal.modulus_zero : ∀ (N : ℕ) [NeZero N], M6.Cyclic.image N (M6.Cyclic.modulus N) = 0 := by
  intro N inst
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Cyclic.modulus N) = 0
  exact AdjoinRoot.mk_self

theorem M7.SignatureIdeal.quotient_membership : ∀ (N : ℕ) [NeZero N], ∀ F p : M6.Cyclic.BinaryPolynomial, F ∣ M6.Cyclic.modulus N → (M6.Cyclic.image N p ∈ M7.SignatureIdeal.principal N F ↔ F ∣ p) := by
  change ∀ (N : ℕ) [NeZero N], ∀ F p : M6.Cyclic.BinaryPolynomial, F ∣ M6.Cyclic.modulus N → (M6.Cyclic.image N p ∈ M7.SignatureIdeal.principal N F ↔ F ∣ p)
  intro N inst F p hF
  change M6.Cyclic.image N p ∈ Ideal.span ({M6.Cyclic.image N F} : Set (M6.Cyclic.CycleRing N)) ↔ F ∣ p
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective x
    subst x
    change AdjoinRoot.mk (M6.Cyclic.modulus N) p = AdjoinRoot.mk (M6.Cyclic.modulus N) F * AdjoinRoot.mk (M6.Cyclic.modulus N) q at hx
    have hz : AdjoinRoot.mk (M6.Cyclic.modulus N) (p - F * q) = 0 := by
      rw [map_sub, map_mul, hx, sub_self]
    have hd : M6.Cyclic.modulus N ∣ p - F * q := AdjoinRoot.mk_eq_zero.mp hz
    have hs : F ∣ (p - F * q) + F * q := dvd_add (hF.trans hd) (dvd_mul_right F q)
    simpa only [sub_add_cancel] using hs
  · rintro ⟨q, rfl⟩
    refine ⟨M6.Cyclic.image N q, ?_⟩
    change AdjoinRoot.mk (M6.Cyclic.modulus N) (F * q) = AdjoinRoot.mk (M6.Cyclic.modulus N) F * AdjoinRoot.mk (M6.Cyclic.modulus N) q
    exact map_mul _ _ _

theorem M7.SignatureIdeal.full_signature_ideal : ∀ (N : ℕ) [NeZero N], ∀ a b : M6.Cyclic.BinaryPolynomial, M7.SignatureIdeal.pairIdeal N a b = M7.SignatureIdeal.principal N (M6.Cyclic.signature a b (M6.Cyclic.modulus N)) := by
  intro N inst a b
  let f : M6.Cyclic.BinaryPolynomial →+* M6.Cyclic.CycleRing N := AdjoinRoot.mk (M6.Cyclic.modulus N)
  change Ideal.span ({f a, f b} : Set (M6.Cyclic.CycleRing N)) = Ideal.span ({f (M6.Cyclic.signature a b (M6.Cyclic.modulus N))} : Set (M6.Cyclic.CycleRing N))
  rcases M6.Cyclic.signature_divides a b (M6.Cyclic.modulus N) with ⟨ha, hb, hm⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    have hmap : ∀ c : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b (M6.Cyclic.modulus N) ∣ c → f c ∈ Ideal.span ({f (M6.Cyclic.signature a b (M6.Cyclic.modulus N))} : Set (M6.Cyclic.CycleRing N)) := by
      intro c hc
      rcases hc with ⟨u, hu⟩
      apply Ideal.mem_span_singleton.mpr
      refine ⟨f u, ?_⟩
      exact (congrArg f hu).trans (map_mul f _ _)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hmap a ha
    · exact hmap b hb
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    rcases M6.Cyclic.signature_bezout a b (M6.Cyclic.modulus N) with ⟨p, q, r, h⟩
    have hz : f (M6.Cyclic.modulus N) = 0 := AdjoinRoot.mk_self
    have he := congrArg f h
    simp only [map_add, map_mul, hz, mul_zero, add_zero] at he
    rw [he]
    apply Ideal.add_mem
    · apply Ideal.mul_mem_left
      exact Ideal.subset_span (by simp)
    · apply Ideal.mul_mem_left
      exact Ideal.subset_span (by simp)

theorem M7.SignatureIdeal.monic_injective : ∀ (N : ℕ) [NeZero N], ∀ F E : M6.Cyclic.BinaryPolynomial, F.Monic → E.Monic → F ∣ M6.Cyclic.modulus N → E ∣ M6.Cyclic.modulus N → (M7.SignatureIdeal.principal N F = M7.SignatureIdeal.principal N E ↔ F = E) := by
  change ∀ (N : ℕ) [NeZero N], ∀ F E : M6.Cyclic.BinaryPolynomial, F.Monic → E.Monic → F ∣ M6.Cyclic.modulus N → E ∣ M6.Cyclic.modulus N → (M7.SignatureIdeal.principal N F = M7.SignatureIdeal.principal N E ↔ F = E)
  intro N inst F E hFm hEm hF hE
  constructor
  · intro h
    have hFE : F ∣ E := by
      apply (M7.SignatureIdeal.quotient_membership N F E hF).mp
      rw [h]
      exact (M7.SignatureIdeal.quotient_membership N E E hE).mpr (dvd_refl E)
    have hEF : E ∣ F := by
      apply (M7.SignatureIdeal.quotient_membership N E F hE).mp
      rw [← h]
      exact (M7.SignatureIdeal.quotient_membership N F F hF).mpr (dvd_refl F)
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hEm hFm hEF
      (Polynomial.natDegree_le_of_dvd hFE hEm.ne_zero)
  · intro h
    subst E
    rfl

theorem M7.SignatureIdeal.principal_gcd : ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, M7.SignatureIdeal.principal N F = M7.SignatureIdeal.principal N (EuclideanDomain.gcd F (M6.Cyclic.modulus N)) := by
  intro N inst F
  let f : M6.Cyclic.BinaryPolynomial →+* M6.Cyclic.CycleRing N := AdjoinRoot.mk (M6.Cyclic.modulus N)
  change Ideal.span ({f F} : Set (M6.Cyclic.CycleRing N)) = Ideal.span ({f (EuclideanDomain.gcd F (M6.Cyclic.modulus N))} : Set (M6.Cyclic.CycleRing N))
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    apply Ideal.mem_span_singleton.mpr
    rcases EuclideanDomain.gcd_dvd_left F (M6.Cyclic.modulus N) with ⟨u, hu⟩
    refine ⟨f u, ?_⟩
    exact (congrArg f hu).trans (map_mul f _ _)
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    have hz : f (M6.Cyclic.modulus N) = 0 := AdjoinRoot.mk_self
    have he := congrArg f (EuclideanDomain.gcd_eq_gcd_ab F (M6.Cyclic.modulus N))
    simp only [map_add, map_mul, hz, zero_mul, add_zero] at he
    apply Ideal.mem_span_singleton.mpr
    exact ⟨f (EuclideanDomain.gcdA F (M6.Cyclic.modulus N)), he⟩
#print axioms M7.SignatureIdeal.modulus_zero
#print axioms M7.SignatureIdeal.full_signature_ideal
#print axioms M7.SignatureIdeal.principal_gcd
#print axioms M7.SignatureIdeal.quotient_membership
#print axioms M7.SignatureIdeal.monic_injective
