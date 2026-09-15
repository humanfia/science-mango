import M6ActualTransferReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.rightIndex N i) = z.2 i
