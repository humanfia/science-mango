import FrozenTarget_2c549c14c311a647
theorem M6.Coordinates.encode_conv : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a h : M6.Physical.Block N), M6.Coordinates.encode N (M6.Physical.conv N a h) = M6.Coordinates.encode N a * M6.Coordinates.encode N h
  intro N inst a h
  classical
  rw [M6.Coordinates.encode_sum, M6.Coordinates.encode_sum, M6.Coordinates.encode_sum]
  simp only [M6.Physical.conv, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  let e : ZMod N ≃ ZMod N :=
    { toFun := fun j => j + r
      invFun := fun k => k - r
      left_inv := by intro j; simp
      right_inv := by intro k; simp }
  have hs := e.sum_comp (fun k : ZMod N =>
    AdjoinRoot.of (M6.Cyclic.modulus N) (a r) *
      AdjoinRoot.of (M6.Cyclic.modulus N) (h (k - r)) *
        M6.Coordinates.rootPow N k)
  rw [← hs]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [e, add_sub_cancel_right, M6.Coordinates.rootPow_add]
  ring
