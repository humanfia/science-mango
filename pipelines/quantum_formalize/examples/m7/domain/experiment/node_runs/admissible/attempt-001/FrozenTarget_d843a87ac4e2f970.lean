import M7Domain

theorem M7.Domain.support_gcd : ∀ (N : ℕ) [NeZero N] (A B : M7.Domain.Support N), Nat.gcd N (((M7.Supports.polynomial A).support ∪ (M7.Supports.polynomial B).support).gcd id) = M7.Domain.connectivityGcd A B := by
  intro N inst A B
  unfold M7.Domain.connectivityGcd
  rw [M7.Supports.support N A, M7.Supports.support N B]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (A B : M7.Domain.Support N), A.card = w → B.card = w → (0 : ZMod N) ∈ A → (0 : ZMod N) ∈ B → M7.Domain.connectivityGcd A B = 1 → M6.Final.Admissible N (M7.Supports.polynomial A) (M7.Supports.polynomial B)
