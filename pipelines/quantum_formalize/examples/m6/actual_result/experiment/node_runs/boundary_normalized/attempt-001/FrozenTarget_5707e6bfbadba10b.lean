import M6ActualResultReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N a b)) (M6.ActualTransfer.boundaryTrace N a b P) = M6.Pinned.enumerator (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P
