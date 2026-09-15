import FrozenTarget_d09314174fe931a8
theorem M6.Transfer.scatter_event_count : QuantumHarnessFrozenTarget := by
  change ∀ R N : ℕ, Fintype.card (M6.Transfer.Memory R) * N * (M6.Transfer.scatterEventList R N).length = M6.Transfer.traceCoefficientOps R N
  intro R N
  classical
  simp [M6.Transfer.scatterEventList, M6.Transfer.traceCoefficientOps, Finset.length_toList, Finset.card_univ]
