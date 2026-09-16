import M8P3Family


def QuantumHarnessFrozenTarget : Prop :=
  M8.P3Family.polynomial ≠ 1 ∧ M8.P3Family.polynomial ≠ 0 ∧ M8.P3Family.polynomial.natDegree = 2
