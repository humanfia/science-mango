import M5ResidueNecessity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (a b F : M5.BinaryPolynomial) (N T : ℕ), T ∣ N → F ∣ M5.cyclicModulus T → M5.completeSignature a b N = F → M5.completeSignature a b T = F
