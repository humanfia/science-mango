import M5ConditionalCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (W : Finset ℕ) (d k : ℕ), (M5.ConditionalCount.restricted W d).powersetCard k = (W.powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s)
