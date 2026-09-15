import FrozenTarget_b6f7d0b2860e1e2a
theorem M6.Flatten.flatten_right : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2 * N)), M6.Flatten.flatten N (M6.Flatten.unflatten N v) = v
  intro N inst v
  funext i
  by_cases h : i.val < N
  · simp only [M6.Flatten.flatten, M6.Flatten.unflatten, if_pos h, dif_pos h]
    apply congrArg v
    apply Fin.ext
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt h]
  · have hi : i.val - N < N := by omega
    simp only [M6.Flatten.flatten, M6.Flatten.unflatten, if_neg h, dif_neg h]
    apply congrArg v
    apply Fin.ext
    simp only [Fin.val_mk, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    omega
