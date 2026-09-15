import FrozenTarget_421235e3f1b4969f
theorem M6.Coordinates.encode_sum : QuantumHarnessFrozenTarget := by
  intro N inst h
  classical
  let e : Fin N ≃ ZMod N :=
    { toFun := fun i => (i.val : ZMod N)
      invFun := fun i => ⟨i.val, ZMod.val_lt i⟩
      left_inv := by
        intro i
        apply Fin.ext
        exact ZMod.val_natCast_of_lt i.isLt
      right_inv := by
        intro i
        exact ZMod.natCast_zmod_val i }
  have hs := e.sum_comp (fun i : ZMod N =>
    AdjoinRoot.of (M6.Cyclic.modulus N) (h i) * M6.Coordinates.rootPow N i)
  simpa [M6.Coordinates.encode, M6.Coordinates.blockPolynomial,
    M6.Cyclic.image, M6.Coordinates.rootPow, e,
    map_sum, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
    ← Polynomial.C_mul_X_pow_eq_monomial,
    ZMod.val_natCast_of_lt] using hs
