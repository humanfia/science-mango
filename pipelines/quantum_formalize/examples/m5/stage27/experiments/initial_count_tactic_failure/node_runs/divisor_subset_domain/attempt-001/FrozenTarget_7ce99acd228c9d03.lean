import M5OrderCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N d k : ℕ), (M5.OrderCount.divisorPositions N d).powersetCard k = ((M5.OrderCount.positivePositions N).powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s)
