import M7Supports

def Frozen_coefficient : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ∀ n : ℕ, (M7.Supports.polynomial A).coeff n = if ∃ i ∈ A, i.val = n then 1 else 0

def Frozen_support : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).support = M7.Supports.natSupport A

def Frozen_support_card : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).support.card = A.card

def Frozen_degree_lt : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).natDegree < N

def Frozen_indicator_coefficient : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ∀ i : ZMod N, (M7.Supports.polynomial A).coeff i.val = M7.Supports.indicator A i

def Frozen_anchor : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ((M7.Supports.polynomial A).coeff 0 = 1 ↔ (0 : ZMod N) ∈ A)

