import FrozenTarget_35ec44b28ca87d82
theorem M6.Coordinates.encode_conv : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a h : M6.Physical.Block N), M6.Coordinates.encode N (M6.Physical.conv N a h) = M6.Coordinates.encode N a * M6.Coordinates.encode N h
  intro N inst a h
  classical
  let f := AdjoinRoot.of (M6.Cyclic.modulus N)
  let p := M6.Coordinates.rootPow N
  calc
    M6.Coordinates.encode N (M6.Physical.conv N a h) =
        ∑ k : ZMod N, ∑ r : ZMod N, f (a r) * f (h (k - r)) * p k := by
      rw [M6.Coordinates.encode_sum]
      simp only [M6.Physical.conv, map_sum, map_mul, Finset.sum_mul, f, p]
    _ = ∑ r : ZMod N, ∑ k : ZMod N, f (a r) * f (h (k - r)) * p k := by
      rw [Finset.sum_comm]
    _ = ∑ r : ZMod N, ∑ j : ZMod N, (f (a r) * p r) * (f (h j) * p j) := by
      apply Finset.sum_congr rfl
      intro r hr
      let e : ZMod N ≃ ZMod N :=
        { toFun := fun j => j + r
          invFun := fun k => k - r
          left_inv := by intro j; simp
          right_inv := by intro k; simp }
      have hs := e.sum_comp (fun k : ZMod N => f (a r) * f (h (k - r)) * p k)
      calc
        (∑ k : ZMod N, f (a r) * f (h (k - r)) * p k) =
            ∑ j : ZMod N, f (a r) * f (h (e j - r)) * p (e j) := hs.symm
        _ = ∑ j : ZMod N, (f (a r) * p r) * (f (h j) * p j) := by
          apply Finset.sum_congr rfl
          intro j hj
          change f (a r) * f (h ((j + r) - r)) * M6.Coordinates.rootPow N (j + r) = _
          rw [add_sub_cancel_right, M6.Coordinates.rootPow_add]
          change f (a r) * f (h j) * (p j * p r) = (f (a r) * p r) * (f (h j) * p j)
          ring
    _ = M6.Coordinates.encode N a * M6.Coordinates.encode N h := by
      rw [M6.Coordinates.encode_sum, M6.Coordinates.encode_sum]
      simp only [Finset.sum_mul, Finset.mul_sum, f, p]
