import M5PolynomialExclusionAccepted
import M5PolynomialIndicator


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → ∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F, p.Monic ∧ Irreducible p
