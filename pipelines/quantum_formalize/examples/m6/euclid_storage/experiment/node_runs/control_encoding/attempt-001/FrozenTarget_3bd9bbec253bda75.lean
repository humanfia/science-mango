import M6EuclidAccepted
import M6EuclidStorage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (width v : ℕ), v ≤ 32*width → v < 2 ^ (M6.EuclidStorage.registerBits width)
