import M7Transport

def Frozen_affine_indicator : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N) (u : (ZMod N)ˣ) (s : ZMod N), M7.Supports.indicator (A.image (M7.Action.affine u s)) = M6.RecipeIsometries.shift N s (M6.RecipeIsometries.multiply N u (M7.Supports.indicator A))

def Frozen_action_isometry : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), Function.Bijective (M7.Transport.Xmap g) ∧ ∀ v : M6.Pinned.Vector (2*N), (M7.Transport.Xmap g v ∈ M7.Transport.BX (M7.Action.act g c) ↔ v ∈ M7.Transport.BX c) ∧ (M7.Transport.Xmap g v ∈ M7.Transport.CX (M7.Action.act g c) ↔ v ∈ M7.Transport.CX c) ∧ M6.Pinned.weight (M7.Transport.Xmap g v) = M6.Pinned.weight v

def Frozen_x_logical : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), ∀ v : M6.Pinned.Vector (2*N), (M7.Transport.Xmap g v ∈ M7.Transport.LX (M7.Action.act g c) ↔ v ∈ M7.Transport.LX c)

def Frozen_z_logical : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), Function.Bijective (M7.Transport.Zmap g) ∧ ∀ v : M6.Pinned.Vector (2*N), (M7.Transport.Zmap g v ∈ M7.Transport.LZ (M7.Action.act g c) ↔ v ∈ M7.Transport.LZ c) ∧ M6.Pinned.weight (M7.Transport.Zmap g v) = M6.Pinned.weight v ∧ M7.Transport.Zmap g (M6.Flatten.J N v) = M6.Flatten.J N (M7.Transport.Xmap g v)

def Frozen_weight_sets : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), (M7.Transport.LX (M7.Action.act g c)).image M6.Pinned.weight = (M7.Transport.LX c).image M6.Pinned.weight

def Frozen_distance_invariant : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), M7.Transport.distance (M7.Action.act g c) = M7.Transport.distance c

def Frozen_actual_witness : Prop :=
  ∀ (N w : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N) (d k : ℕ) (v : M6.Pinned.Vector (2*N)), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Domain.connectivityGcd c.1 c.2 = 1 → M6.ActualTransfer.solve N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) = some (d,v,k) → M7.Transport.distance (M7.Action.act g c) = some d ∧ M7.Transport.Xmap g v ∈ M7.Transport.LX (M7.Action.act g c) ∧ M6.Pinned.weight (M7.Transport.Xmap g v) = d ∧ M6.Flatten.J N (M7.Transport.Xmap g v) ∈ M7.Transport.LZ (M7.Action.act g c) ∧ M6.Pinned.weight (M6.Flatten.J N (M7.Transport.Xmap g v)) = d ∧ k ≤ 2*N

