import M6TraceCountsReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.ActualTransfer.boundaryTrace N a b P = ∑ h : M6.Transfer.Input N, M6.Character.pinnedMonomial P (M6.Flatten.flatten N (M6.Physical.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h))
