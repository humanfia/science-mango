import FrozenTarget_7456aeb56a36b416
theorem M6.ActualTransfer.left_coordinate : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.leftIndex N i) = z.1 i
  intro N inst z i
  simp [M6.Flatten.flatten, M6.ActualTransfer.leftIndex, ZMod.val_lt i]
