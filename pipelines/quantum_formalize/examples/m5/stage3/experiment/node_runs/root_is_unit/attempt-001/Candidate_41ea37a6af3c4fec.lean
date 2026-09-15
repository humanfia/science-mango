import FrozenTarget_41ea37a6af3c4fec
theorem M5.Period.root_is_unit : QuantumHarnessFrozenTarget := by
  change ∀ (F : M5.BinaryPolynomial), F.coeff 0 = 1 → IsUnit (AdjoinRoot.root F)
  intro F hF
  have h : AdjoinRoot.root F * AdjoinRoot.mk F F.divX + 1 = 0 := by
    simpa only [map_add, map_mul, hF, Polynomial.C_1, map_one,
      AdjoinRoot.mk_self, AdjoinRoot.root] using
      congrArg (AdjoinRoot.mk F) (Polynomial.X_mul_divX_add F)
  have hinv : AdjoinRoot.root F * (-AdjoinRoot.mk F F.divX) = 1 := by
    rw [mul_neg, eq_neg_of_add_eq_zero_left h, neg_neg]
  exact ⟨⟨AdjoinRoot.root F, -AdjoinRoot.mk F F.divX,
    hinv, by rw [mul_comm]; exact hinv⟩, rfl⟩
