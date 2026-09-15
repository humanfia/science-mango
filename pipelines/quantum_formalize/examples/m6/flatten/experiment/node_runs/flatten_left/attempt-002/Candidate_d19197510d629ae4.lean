import FrozenTarget_d19197510d629ae4
theorem M6.Flatten.flatten_left : QuantumHarnessFrozenTarget := by
  intro N _ z
  apply Prod.ext
  · funext i
    have hi : i.val < N := ZMod.val_lt i
    simp [M6.Flatten.unflatten, M6.Flatten.flatten, hi]
  · funext i
    have hi : ¬ N + i.val < N := by omega
    simp [M6.Flatten.unflatten, M6.Flatten.flatten, hi, Nat.add_sub_cancel_left]
