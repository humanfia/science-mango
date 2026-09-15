import FrozenTarget_5964e07be57dfefc
theorem M7.SignatureIdeal.quotient_membership : QuantumHarnessFrozenTarget := by
  by
    intro N inst F p hF
    unfold M7.SignatureIdeal.principal
    rw [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨x, hx⟩
      have hs : Function.Surjective (AdjoinRoot.mk (M6.Cyclic.modulus N)) := by
        first
        | exact AdjoinRoot.mk_surjective _
        | exact AdjoinRoot.mk_surjective
      obtain ⟨q, rfl⟩ := hs x
      change AdjoinRoot.mk (M6.Cyclic.modulus N) p =
        AdjoinRoot.mk (M6.Cyclic.modulus N) F *
          AdjoinRoot.mk (M6.Cyclic.modulus N) q at hx
      have hz : AdjoinRoot.mk (M6.Cyclic.modulus N) (p - F * q) = 0 := by
        rw [map_sub, map_mul, hx, sub_self]
      have hm : M6.Cyclic.modulus N ∣ p - F * q :=
        (AdjoinRoot.mk_eq_zero).mp hz
      have hd : F ∣ p - F * q := dvd_trans hF hm
      have ha := dvd_add hd (dvd_mul_right F q)
      simpa only [sub_add_cancel] using ha
    · rintro ⟨q, rfl⟩
      refine ⟨M6.Cyclic.image N q, ?_⟩
      change AdjoinRoot.mk (M6.Cyclic.modulus N) (F * q) =
        AdjoinRoot.mk (M6.Cyclic.modulus N) F *
          AdjoinRoot.mk (M6.Cyclic.modulus N) q
      exact map_mul _ _ _
