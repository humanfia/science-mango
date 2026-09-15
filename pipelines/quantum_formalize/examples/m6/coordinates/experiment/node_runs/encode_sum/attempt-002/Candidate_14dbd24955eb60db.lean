import FrozenTarget_14dbd24955eb60db
theorem M6.Coordinates.encode_sum : QuantumHarnessFrozenTarget := by
  intro N inst h
  classical
  let e : Fin N ≃ ZMod N :=
    { toFun := fun i => (i.val : ZMod N)
      invFun := fun i => ⟨i.val, ZMod.val_lt i⟩
      left_inv := by
        intro i
        apply Fin.ext
        exact (ZMod.val_natCast N i.val).trans (Nat.mod_eq_of_lt i.isLt)
      right_inv := fun i => ZMod.natCast_zmod_val i }
  have hv (i : Fin N) : (i.val : ZMod N).val = i.val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  have hs := e.sum_comp (fun i : ZMod N =>
    AdjoinRoot.of (M6.Cyclic.modulus N) (h i) *
      AdjoinRoot.root (M6.Cyclic.modulus N) ^ i.val)
  change (∑ i : Fin N,
    AdjoinRoot.of (M6.Cyclic.modulus N) (h (i.val : ZMod N)) *
      AdjoinRoot.root (M6.Cyclic.modulus N) ^ (i.val : ZMod N).val) = _ at hs
  simp only [hv] at hs
  simpa only [M6.Coordinates.encode, M6.Coordinates.blockPolynomial,
    M6.Cyclic.image, M6.Coordinates.rootPow, map_sum, map_mul, map_pow,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X] using hs
