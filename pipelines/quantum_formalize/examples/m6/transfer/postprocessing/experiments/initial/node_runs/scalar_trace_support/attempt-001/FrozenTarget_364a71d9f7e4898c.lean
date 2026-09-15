import M6Postprocessing


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : ℕ), 2*N < d → (M6.Transfer.scalarTracePolynomial W N).coeff d = 0
