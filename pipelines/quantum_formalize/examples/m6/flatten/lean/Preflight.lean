import M6Flatten
def check_0 : Prop := ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Flatten.unflatten N (M6.Flatten.flatten N z) = z
def check_1 : Prop := ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)), M6.Flatten.flatten N (M6.Flatten.unflatten N v) = v
def check_2 : Prop := ∀ (N : ℕ) (z w : M6.Physical.Word N), M6.Flatten.flatten N (z+w) = M6.Flatten.flatten N z + M6.Flatten.flatten N w
def check_3 : Prop := ∀ (N : ℕ) (c : ZMod 2) (z : M6.Physical.Word N), M6.Flatten.flatten N (c • z) = c • M6.Flatten.flatten N z
def check_4 : Prop := ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Pinned.weight (M6.Flatten.flatten N z) = M6.Physical.wordWeight N z
def check_5 : Prop := ∀ (N : ℕ) [NeZero N] (z w : M6.Physical.Word N), M6.Character.dot (M6.Flatten.flatten N z) (M6.Flatten.flatten N w) = M6.Physical.pairing N z w
def check_6 : Prop := ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)), M6.Flatten.J N (M6.Flatten.J N v) = v
def check_7 : Prop := ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)), M6.Pinned.weight (M6.Flatten.J N v) = M6.Pinned.weight v
def check_8 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ↔ ∀ h : M6.Physical.Block N, M6.Character.dot (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))) v = 0
