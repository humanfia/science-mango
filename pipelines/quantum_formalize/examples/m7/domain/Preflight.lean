import M7Domain

def Frozen_coefficients_indicator : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), M6.Coordinates.coefficients N (M7.Supports.polynomial A) = M7.Supports.indicator A

def Frozen_block_polynomial : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), M6.Coordinates.blockPolynomial N (M7.Supports.indicator A) = M7.Supports.polynomial A

def Frozen_support_gcd : Prop :=
  ∀ (N : ℕ) [NeZero N] (A B : M7.Domain.Support N), Nat.gcd N (((M7.Supports.polynomial A).support ∪ (M7.Supports.polynomial B).support).gcd id) = M7.Domain.connectivityGcd A B

def Frozen_admissible : Prop :=
  ∀ (N w : ℕ) [NeZero N] (A B : M7.Domain.Support N), A.card = w → B.card = w → (0 : ZMod N) ∈ A → (0 : ZMod N) ∈ B → M7.Domain.connectivityGcd A B = 1 → M6.Final.Admissible N (M7.Supports.polynomial A) (M7.Supports.polynomial B)

def Frozen_shift_card : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), ∀ r : ZMod N, (M7.Domain.shift A r).card = A.card

def Frozen_shift_anchor : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), ∀ q : ZMod N, q ∈ A → (0 : ZMod N) ∈ M7.Domain.shift A (-q)

