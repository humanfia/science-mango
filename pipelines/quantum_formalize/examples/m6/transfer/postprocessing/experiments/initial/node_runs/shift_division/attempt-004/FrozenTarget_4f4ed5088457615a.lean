import M6Postprocessing


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2:ℤ)^k
