import FrozenTarget_7528fb43e07ccfde
theorem M7.SignatureIdeal.quotient_membership : QuantumHarnessFrozenTarget := by
  intro N inst F p hF
  change M6.Cyclic.image N p ∈ Ideal.span ({M6.Cyclic.image N F} : Set (M6.Cyclic.CycleRing N)) ↔ F ∣ p
  rw [Ideal.mem_span_singleton]
  change AdjoinRoot.mk (M6.Cyclic.modulus N) F ∣ AdjoinRoot.mk (M6.Cyclic.modulus N) p ↔ F ∣ p
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (M6.Cyclic.modulus N) x
    have heq : AdjoinRoot.mk (M6.Cyclic.modulus N) p = AdjoinRoot.mk (M6.Cyclic.modulus N) (F * q) := by
      simpa only [map_mul] using hx
    have hd : F ∣ p - F * q := hF.trans (AdjoinRoot.mk_eq_mk.mp heq)
    have hprod : F ∣ F * q := ⟨q, rfl⟩
    simpa only [sub_add_cancel] using hd.add hprod
  · rintro ⟨q, hq⟩
    refine ⟨AdjoinRoot.mk (M6.Cyclic.modulus N) q, ?_⟩
    rw [hq, map_mul]
