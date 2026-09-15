import FrozenTarget_5a9f3094c1046395
theorem M7.QuotientDegree.quotient_equiv : QuantumHarnessFrozenTarget := by
  intro N _ F hF
  let f : M6.Cyclic.CycleRing N →+* AdjoinRoot F :=
    Ideal.Quotient.factor (M7.QuotientDegree.span_containment N F hF)
  have hk : RingHom.ker f = M7.SignatureIdeal.principal N F := by
    ext x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change AdjoinRoot.mk F p = 0 ↔ M6.Cyclic.image N p ∈ M7.SignatureIdeal.principal N F
    rw [AdjoinRoot.mk_eq_zero]
    exact (M7.SignatureIdeal.quotient_membership N F p hF).symm
  rw [← hk]
  exact ⟨RingHom.quotientKerEquivOfSurjective (f := f)
    (Ideal.Quotient.factor_surjective (M7.QuotientDegree.span_containment N F hF))⟩
