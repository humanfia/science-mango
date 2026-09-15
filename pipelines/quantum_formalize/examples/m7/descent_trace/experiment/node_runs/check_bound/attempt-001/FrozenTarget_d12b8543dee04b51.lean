import M7DescentTrace


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).2 ≤ 2*ss.length
