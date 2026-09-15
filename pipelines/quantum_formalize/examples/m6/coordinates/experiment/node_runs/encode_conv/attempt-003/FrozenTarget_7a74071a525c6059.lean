import M6Coordinates

theorem M6.Coordinates.encode_sum : ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N), M6.Coordinates.encode N h = ∑ i : ZMod N, AdjoinRoot.of (M6.Cyclic.modulus N) (h i) * M6.Coordinates.rootPow N i := by
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

theorem M6.Coordinates.root_period : ∀ (N : ℕ) [NeZero N], (AdjoinRoot.root (M6.Cyclic.modulus N))^N = 1 := by
  change ∀ (N : ℕ) [NeZero N], (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ N = 1
  intro N hN
  have h := AdjoinRoot.eval₂_root (M6.Cyclic.modulus N)
  change Polynomial.eval₂ (AdjoinRoot.of (M6.Cyclic.modulus N)) (AdjoinRoot.root (M6.Cyclic.modulus N)) (Polynomial.X ^ N + 1) = 0 at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one] at h
  have h₂ : (1 : ZMod 2) + 1 = 0 := by decide
  have h₂' : (1 : AdjoinRoot (M6.Cyclic.modulus N)) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg (AdjoinRoot.of (M6.Cyclic.modulus N)) h₂
  exact add_right_cancel (h.trans h₂'.symm)

theorem M6.Coordinates.rootPow_add : ∀ (N : ℕ) [NeZero N] (i j : ZMod N), M6.Coordinates.rootPow N (i+j) = M6.Coordinates.rootPow N i * M6.Coordinates.rootPow N j := by
  change ∀ (N : ℕ) [NeZero N] (i j : ZMod N), M6.Coordinates.rootPow N (i + j) = M6.Coordinates.rootPow N i * M6.Coordinates.rootPow N j
  intro N hN i j
  change (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ (i + j).val = (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ i.val * (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ j.val
  rw [ZMod.val_add, ← pow_add]
  have h := congrArg (fun k : ℕ => (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ k) (Nat.mod_add_div (i.val + j.val) N)
  simpa only [pow_add, pow_mul, M6.Coordinates.root_period, one_pow, mul_one] using h
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a h : M6.Physical.Block N), M6.Coordinates.encode N (M6.Physical.conv N a h) = M6.Coordinates.encode N a * M6.Coordinates.encode N h
