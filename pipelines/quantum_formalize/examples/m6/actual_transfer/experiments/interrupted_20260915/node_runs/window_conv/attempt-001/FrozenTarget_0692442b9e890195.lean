import M6ActualTransferReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) [NeZero N] (a : M6.ActualTransfer.BP), a.natDegree ≤ R → R < N → ∀ (h : M6.Transfer.Input N) (i : ZMod N), M6.Transfer.cyclicOutput (M6.ActualTransfer.window R a) h i = M6.Physical.conv N (M6.Coordinates.coefficients N a) h i
