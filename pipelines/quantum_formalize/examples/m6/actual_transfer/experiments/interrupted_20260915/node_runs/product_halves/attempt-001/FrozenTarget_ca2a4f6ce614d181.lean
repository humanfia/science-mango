import M6ActualTransferReady

theorem M6.ActualTransfer.left_coordinate : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.leftIndex N i) = z.1 i := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.leftIndex N i) = z.1 i
  intro N inst z i
  simp [M6.Flatten.flatten, M6.ActualTransfer.leftIndex, ZMod.val_lt i]

theorem M6.ActualTransfer.right_coordinate : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.rightIndex N i) = z.2 i := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.rightIndex N i) = z.2 i
  intro N inst z i
  have h₁ : ¬ N + i.val < N := by omega
  have h₂ : ¬ i.val + N < N := by omega
  simp [M6.Flatten.flatten, M6.ActualTransfer.rightIndex, h₁, h₂]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (w : Fin (2*N) → ZMod 2 → Polynomial ℤ), (∏ q, w q (M6.Flatten.flatten N z q)) = ∏ i : ZMod N, w (M6.ActualTransfer.leftIndex N i) (z.1 i) * w (M6.ActualTransfer.rightIndex N i) (z.2 i)
