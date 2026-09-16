import M8P4Family


def QuantumHarnessFrozenTarget : Prop :=
  M8.P4Family.polynomial ≠ 1 ∧ M8.P4Family.polynomial ≠ 0 ∧ M8.P4Family.polynomial.natDegree = 3
