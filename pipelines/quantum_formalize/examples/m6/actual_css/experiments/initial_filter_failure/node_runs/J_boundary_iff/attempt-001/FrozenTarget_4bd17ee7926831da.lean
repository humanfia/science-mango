import M6ActualCSS
import M6ActualCSSDependencies


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.Spaces.boundaryWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.subspaceWords (M6.Spaces.D N a b)
