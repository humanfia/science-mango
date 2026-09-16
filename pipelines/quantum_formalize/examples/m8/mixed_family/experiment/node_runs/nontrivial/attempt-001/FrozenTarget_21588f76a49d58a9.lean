import M8MixedFamily


def QuantumHarnessFrozenTarget : Prop :=
  M8.MixedFamily.a ≠ 1 ∧ M8.MixedFamily.a ≠ 0 ∧ (M8.MixedFamily.a*M8.MixedFamily.b).natDegree = 3
