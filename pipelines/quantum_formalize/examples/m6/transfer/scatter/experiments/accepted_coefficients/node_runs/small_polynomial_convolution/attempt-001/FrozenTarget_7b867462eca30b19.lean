import M6TransferScatter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (p q : Polynomial ℤ) (d : ℕ), q.natDegree ≤ 2 → (p*q).coeff d = ∑ e : Fin 3, if e.val ≤ d then p.coeff (d-e.val) * q.coeff e.val else 0
