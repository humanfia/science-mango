import M7GenerationCalls


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).2 = 2*n
