import M6Physical
def check_0 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Physical.conv N a b = M6.Physical.conv N b a
def check_1 : Prop := ∀ (N : ℕ) [NeZero N] (a u v : M6.Physical.Block N), M6.Physical.conv N a (u+v) = M6.Physical.conv N a u + M6.Physical.conv N a v
def check_2 : Prop := ∀ (N : ℕ) [NeZero N] (a b c : M6.Physical.Block N), M6.Physical.conv N a (M6.Physical.conv N b c) = M6.Physical.conv N (M6.Physical.conv N a b) c
def check_3 : Prop := ∀ (N : ℕ) (a : M6.Physical.Block N), M6.Physical.rev N (M6.Physical.rev N a) = a
def check_4 : Prop := ∀ (N : ℕ) [NeZero N] (a : M6.Physical.Block N) (i : ZMod N), M6.Physical.dot N (M6.Physical.delta N i) a = a i
def check_5 : Prop := ∀ (N : ℕ) [NeZero N] (a : M6.Physical.Block N), M6.Physical.weight N (M6.Physical.rev N a) = M6.Physical.weight N a
def check_6 : Prop := ∀ (N : ℕ) (z : M6.Physical.Word N), M6.Physical.J N (M6.Physical.J N z) = z
def check_7 : Prop := ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Physical.wordWeight N (M6.Physical.J N z) = M6.Physical.wordWeight N z
def check_8 : Prop := ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Physical.syndrome N a b (M6.Physical.boundary N a b h) = 0
def check_9 : Prop := ∀ (N : ℕ) [NeZero N] (a h u : M6.Physical.Block N), M6.Physical.dot N (M6.Physical.rev N (M6.Physical.conv N a h)) u = M6.Physical.dot N (M6.Physical.rev N h) (M6.Physical.conv N a u)
def check_10 : Prop := ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N) (z : M6.Physical.Word N), M6.Physical.pairing N (M6.Physical.J N (M6.Physical.boundary N a b h)) z = M6.Physical.dot N (M6.Physical.rev N h) (M6.Physical.syndrome N a b z)
def check_11 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (z : M6.Physical.Word N), M6.Physical.syndrome N a b z = 0 ↔ ∀ h : M6.Physical.Block N, M6.Physical.pairing N (M6.Physical.J N (M6.Physical.boundary N a b h)) z = 0
