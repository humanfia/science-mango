import FrozenTarget_7833c0b44b546d64
theorem M6.Coordinates.encode_conv : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a h : M6.Physical.Block N), M6.Coordinates.encode N (M6.Physical.conv N a h) = M6.Coordinates.encode N a * M6.Coordinates.encode N h
  intro N inst a h
  classical
  simp only [M6.Coordinates.encode_sum, M6.Physical.conv, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  let e : ZMod N ≃ ZMod N :=
    { toFun := fun j => j + r
      invFun := fun k => k - r
      left_inv := fun j => add_sub_cancel_right j r
      right_inv := fun k => sub_add_cancel k r }
  have hs := e.sum_comp (fun k : ZMod N =>
    (AdjoinRoot.of (M6.Cyclic.modulus N) (a r) *
      AdjoinRoot.of (M6.Cyclic.modulus N) (h (k - r))) *
      M6.Coordinates.rootPow N k)
  calc
    _ = ∑ j : ZMod N,
        (AdjoinRoot.of (M6.Cyclic.modulus N) (a r) *
          AdjoinRoot.of (M6.Cyclic.modulus N) (h ((j + r) - r))) *
          M6.Coordinates.rootPow N (j + r) := hs.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [add_sub_cancel_right, M6.Coordinates.rootPow_add]
      ring
