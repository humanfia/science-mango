import M6ActualCounts
import M6ActualCountsDependencies


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h : M6.Physical.Block N, (M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N a) h), M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N b) h)) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h)
