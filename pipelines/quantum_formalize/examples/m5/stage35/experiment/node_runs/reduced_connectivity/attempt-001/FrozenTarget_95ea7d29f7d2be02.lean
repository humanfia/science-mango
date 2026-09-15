import M5ResidueNecessity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w N T : ℕ) (hT : 0 < T) (u v : Fin w → ℕ), T ∣ N → M5.Connectivity.supportGcd N (Finset.univ.image u) (Finset.univ.image v) = 1 → M5.BoundedConstruction.tupleSupportGcd (M5.ResidueNecessity.reduceTuple T hT u) (M5.ResidueNecessity.reduceTuple T hT v) = 1
