import M6TransferPartialResourcesReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (p : Polynomial ℤ) (L : ℕ), (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ M6.Transfer.polynomialMass p
