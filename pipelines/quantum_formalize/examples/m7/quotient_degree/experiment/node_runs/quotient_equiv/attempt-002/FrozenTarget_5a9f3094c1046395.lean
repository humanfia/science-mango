import M7QuotientDegree

theorem M7.QuotientDegree.span_containment : ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F ∣ M6.Cyclic.modulus N → Ideal.span ({M6.Cyclic.modulus N} : Set M6.Cyclic.BinaryPolynomial) ≤ Ideal.span ({F} : Set M6.Cyclic.BinaryPolynomial) := by
  intro N _ F hF
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  exact Ideal.mem_span_singleton.mpr hF
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F ∣ M6.Cyclic.modulus N → Nonempty ((M6.Cyclic.CycleRing N ⧸ M7.SignatureIdeal.principal N F) ≃+* AdjoinRoot F)
