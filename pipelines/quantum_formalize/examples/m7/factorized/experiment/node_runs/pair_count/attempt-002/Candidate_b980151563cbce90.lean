import FrozenTarget_b980151563cbce90
theorem M7.Factorized.pair_count : QuantumHarnessFrozenTarget := by
  intro S T instS instT left right
  classical
  unfold M7.Factorized.count
  rw [← Finset.card_product]
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
