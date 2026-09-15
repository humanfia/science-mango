import FrozenTarget_fc63ed0470ae647d
theorem M5.TupleCompletion.divisibility_sum : QuantumHarnessFrozenTarget := by
  intro P Z T d k t
  have hneg : -Z = Z := by
    ext n
    simp only [Polynomial.coeff_neg]
    have h : ∀ a : ZMod 2, -a = a := by decide
    exact h (Z.coeff n)
  rw [AdjoinRoot.mk_eq_mk, sub_eq_add_neg, hneg, add_comm]
