import M6TransferCoefficients


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start finish : M6.Transfer.Memory R) (n : ℕ), (∀ i m t, (W i m t).natDegree ≤ 2) → (M6.Transfer.layers W start n finish).natDegree ≤ 2*n
