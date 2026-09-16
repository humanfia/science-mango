import M8P4Gcd


def QuantumHarnessFrozenTarget : Prop :=
  ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1
