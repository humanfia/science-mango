import M6ActualCSS
import M6ActualCSSDependencies
open scoped BigOperators
#check (∀ (N : ℕ) [NeZero N] (v w : M6.Pinned.Vector (2*N)), M6.Character.dot (M6.Flatten.J N v) (M6.Flatten.J N w) = M6.Character.dot v w)
#check (∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.Spaces.boundaryWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.subspaceWords (M6.Spaces.D N a b))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.dualWords (M6.Spaces.B N a b))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (0 : M6.Pinned.Vector (2*N)) ∈ M6.Spaces.boundaryWords N a b ∧ (0 : M6.Pinned.Vector (2*N)) ∈ M6.Character.subspaceWords (M6.Spaces.D N a b))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Character.subspaceWords (M6.Spaces.D N a b) ⊆ M6.Character.dualWords (M6.Spaces.B N a b))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.CSS.logical (M6.Spaces.boundaryWords N a b) (M6.Spaces.cycleWords N a b) ↔ M6.Flatten.J N v ∈ M6.CSS.logical (M6.Character.subspaceWords (M6.Spaces.D N a b)) (M6.Character.dualWords (M6.Spaces.B N a b)))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.CSS.quantumDistance (M6.Spaces.boundaryWords N a b) (M6.Spaces.cycleWords N a b) (M6.Character.subspaceWords (M6.Spaces.D N a b)) (M6.Character.dualWords (M6.Spaces.B N a b)) = M6.Pinned.distance (M6.Spaces.logicalWords N a b))
