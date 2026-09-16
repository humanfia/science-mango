import M8AntipodalFamily


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (v : ℕ), 3 ≤ v → M8.AntipodalFamily.polynomial (2^v) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^(v-1)+1)
