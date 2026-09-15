import M7Action
def target_0 : Prop := ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.identity N) g = g
def target_1 : Prop := ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose g (M7.Action.identity N) = g
def target_2 : Prop := ∀ (N : ℕ) [NeZero N], ∀ g h k : M7.Action.Record N, M7.Action.compose (M7.Action.compose g h) k = M7.Action.compose g (M7.Action.compose h k)
def target_3 : Prop := ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.inverse g) g = M7.Action.identity N
def target_4 : Prop := ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose g (M7.Action.inverse g) = M7.Action.identity N
def target_5 : Prop := ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (s : ZMod N), Function.Bijective (M7.Action.affine u s)
def target_6 : Prop := ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.Action.identity N) c = c
def target_7 : Prop := ∀ (N : ℕ) [NeZero N], ∀ (g h : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.compose g h) c = M7.Action.act g (M7.Action.act h c)
def target_8 : Prop := ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.inverse g) (M7.Action.act g c) = c
def target_9 : Prop := ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), (M7.Action.act g c).1.card = (if g.exchange then c.2.card else c.1.card) ∧ (M7.Action.act g c).2.card = (if g.exchange then c.1.card else c.2.card)
def target_10 : Prop := ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.translate g.leftShift g.rightShift) (M7.Action.compose (M7.Action.multiplier g.unit) (if g.exchange then M7.Action.exchange N else M7.Action.identity N)) = g
def target_11 : Prop := ∀ (N : ℕ) [NeZero N], Fintype.card (M7.Action.Record N) = Nat.totient N * 2 * N * N
def target_12 : Prop := Fintype.card (M7.Action.Record 1) = 2
