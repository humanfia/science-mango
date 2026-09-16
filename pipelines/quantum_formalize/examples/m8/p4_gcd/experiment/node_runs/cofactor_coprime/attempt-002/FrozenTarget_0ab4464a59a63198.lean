import M8P4Gcd

theorem M8.P4Gcd.cofactor_eval : ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1 := by
  change ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1
  intro m
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [M8.P4Gcd.oddCofactor, Polynomial.eval_finset_sum, Nat.cast_add, Nat.cast_mul, htwo]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ m : ℕ, IsCoprime (Polynomial.X+1) (M8.P4Gcd.oddCofactor m)
