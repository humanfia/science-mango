import FrozenTarget_291b399c03dbecc6
theorem M7.QuotientDegree.quotient_equiv : QuantumHarnessFrozenTarget := by
  intro N _ F hF
  let h := M7.QuotientDegree.span_containment N F hF
  let f : M6.Cyclic.CycleRing N →+* AdjoinRoot F := Ideal.Quotient.factor h
  have hk : RingHom.ker f = M7.SignatureIdeal.principal N F := by
    ext x
    have hs : Function.Surjective (Ideal.Quotient.mk (Ideal.span ({M6.Cyclic.modulus N} : Set M6.Cyclic.BinaryPolynomial))) := Ideal.Quotient.mk_surjective
    obtain ⟨p, rfl⟩ := hs x
    change Ideal.Quotient.factor h (Ideal.Quotient.mk _ p) = 0 ↔ _
    rw [Ideal.Quotient.factor_mk]
    change AdjoinRoot.mk F p = 0 ↔ M6.Cyclic.image N p ∈ M7.SignatureIdeal.principal N F
    rw [AdjoinRoot.mk_eq_zero, M7.SignatureIdeal.quotient_membership N F p hF]
  have hs : Function.Surjective f := Ideal.Quotient.factor_surjective h
  rw [← hk]
  exact ⟨RingHom.quotientKerEquivOfSurjective f hs⟩
