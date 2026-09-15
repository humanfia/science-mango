import M6IndexedArrayReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) [NeZero N] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ), R < N → (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → (∀ i m t, (W i m t).natDegree ≤ 2) → M6.Transfer.IndexedArrayGuarantee R N W
