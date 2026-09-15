import M6EuclidAccepted
import M6EuclidStorage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, M6.EuclidStorage.polynomialSlots.length = 4 ∧ M6.EuclidStorage.controlSlots.length = 16 ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512*(N+1)^2
