import M5SignatureCongruence

theorem M5.SignatureCongruence.divisibility_of_quotient_eq : ∀ (D a a' : M5.BinaryPolynomial) (T : ℕ), D ∣ M5.cyclicModulus T → AdjoinRoot.mk (M5.cyclicModulus T) a = AdjoinRoot.mk (M5.cyclicModulus T) a' → (D ∣ a ↔ D ∣ a') := by
  change ∀ (D a a' : M5.BinaryPolynomial) (T : ℕ), D ∣ M5.cyclicModulus T → AdjoinRoot.mk (M5.cyclicModulus T) a = AdjoinRoot.mk (M5.cyclicModulus T) a' → (D ∣ a ↔ D ∣ a')
  intro D a a' T hD heq
  have hmod : M5.cyclicModulus T ∣ a - a' := by
    simpa only [AdjoinRoot.mk_eq_mk] using heq
  have hdiff : D ∣ a - a' := dvd_trans hD hmod
  constructor
  · intro ha
    have hid : a - (a - a') = a' := by ring
    rw [← hid]
    exact dvd_sub ha hdiff
  · intro ha'
    simpa only [sub_add_cancel] using dvd_add hdiff ha'
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (a b a' b' : M5.BinaryPolynomial) (T : ℕ), AdjoinRoot.mk (M5.cyclicModulus T) a = AdjoinRoot.mk (M5.cyclicModulus T) a' → AdjoinRoot.mk (M5.cyclicModulus T) b = AdjoinRoot.mk (M5.cyclicModulus T) b' → M5.completeSignature a b T = M5.completeSignature a' b' T
