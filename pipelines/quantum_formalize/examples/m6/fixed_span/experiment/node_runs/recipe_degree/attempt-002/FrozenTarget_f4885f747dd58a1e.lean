import M6FixedSpan


def QuantumHarnessFrozenTarget : Prop :=
  M6.FixedSpan.recipe.Monic ∧ M6.FixedSpan.recipe.natDegree = 2
