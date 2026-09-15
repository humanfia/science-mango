import FrozenTarget_7a74071a525c6059
theorem M6.Coordinates.encode_conv : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a h : M6.Physical.Block N), M6.Coordinates.encode N (M6.Physical.conv N a h) = M6.Coordinates.encode N a * M6.Coordinates.encode N h
  intro N inst a h
  classical
  rw [M6.Coordinates.encode_sum, M6.Coordinates.encode_sum, M6.Coordinates.encode_sum]
  simp only [M6.Physical.conv, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  let e : ZMod N ≃ ZMod N :=
    { toFun := fun j => j + r
      invFun := fun k => k - r
      left_inv := by intro j; simp
      right_inv := by intro k; simp }
  have hs := e.sum_comp (fun i : ZMod N =>
    AdjoinRoot.of (M6.Cyclic.modulus N) (a r) *
      AdjoinRoot.of (M6.Cyclic.modulus N) (h (i - r)) *
      M6.Coordinates.rootPow N i)
  refine hs.symm.trans ?_
  apply Finset.sum_congr rfl
  intro j hj
  change AdjoinRoot.of (M6.Cyclic.modulus N) (a r) *
    AdjoinRoot.of (M6.Cyclic.modulus N) (h ((j + r) - r)) *
    M6.Coordinates.rootPow N (j + r) = _
  simp only [add_sub_cancel_right, M6.Coordinates.rootPow_add]
  ring
