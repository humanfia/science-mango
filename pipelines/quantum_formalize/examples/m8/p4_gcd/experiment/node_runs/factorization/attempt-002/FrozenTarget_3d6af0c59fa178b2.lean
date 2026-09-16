import M8P4Gcd


def QuantumHarnessFrozenTarget : Prop :=
  ∀ m : ℕ, M6.Cyclic.modulus (4*m+2) = (Polynomial.X+1)^2 * M8.P4Gcd.oddCofactor m
