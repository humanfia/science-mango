import FrozenTarget_d3c0f6e763b2b8a4
theorem M6.Flatten.flatten_left : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Flatten.unflatten N (M6.Flatten.flatten N z) = z
  intro N inst z
  apply Prod.ext
  · funext i
    have hi := ZMod.val_lt i
    simp [M6.Flatten.unflatten, M6.Flatten.flatten, hi, ZMod.cast_val]
  · funext i
    have hi : ¬ N + i.val < N := by omega
    have hi' : ¬ i.val + N < N := by omega
    simp [M6.Flatten.unflatten, M6.Flatten.flatten, hi, hi', Nat.add_sub_cancel_left, ZMod.cast_val]
