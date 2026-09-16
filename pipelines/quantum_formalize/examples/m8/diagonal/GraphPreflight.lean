import M8Diagonal
def target_0 : Prop := (∀ (N : ℕ) [NeZero N], ∀ a : M6.Physical.Block N, M6.Physical.weight N a = 0 ↔ a = 0)
def target_1 : Prop := (∀ (N : ℕ) [NeZero N], ∀ a : M6.Physical.Block N, M6.Physical.weight N a = 1 ↔ ∃ j : ZMod N, a = M6.Physical.delta N j)
def target_2 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (p : M6.Physical.Block N) (j i : ZMod N), M6.Physical.conv N p (M6.Physical.delta N j) i = p (i-j))
def target_3 : Prop := (∀ (N : ℕ) [NeZero N], ∀ j : ZMod N, M6.Physical.weight N (M6.Physical.delta N j) = 1)
def target_4 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (p : M6.Physical.Block N) (z : M6.Physical.Word N), p ≠ 0 → M6.Physical.syndrome N p p z = 0 → M6.Physical.wordWeight N z < 2 → z = 0)
def target_5 : Prop := (∀ (N : ℕ) [NeZero N], ∀ p : M6.Physical.Block N, M8.Diagonal.DeltaNotImage N p → (M6.Flatten.flatten N (M6.Physical.delta N 0, M6.Physical.delta N 0) ∈ M6.Spaces.logicalWords N p p ∧ M6.Pinned.weight (M6.Flatten.flatten N (M6.Physical.delta N 0, M6.Physical.delta N 0)) = 2))
def target_6 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (p : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), p ≠ 0 → v ∈ M6.Spaces.logicalWords N p p → 2 ≤ M6.Pinned.weight v)
def target_7 : Prop := (∀ (N : ℕ) [NeZero N], ∀ p : M6.Physical.Block N, p ≠ 0 → M8.Diagonal.DeltaNotImage N p → M8.Diagonal.distance N p = some 2)
