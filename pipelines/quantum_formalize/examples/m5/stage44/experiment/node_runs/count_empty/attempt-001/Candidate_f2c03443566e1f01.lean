import FrozenTarget_f2c03443566e1f01
theorem M5.PrefixPartition.count_empty : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ)
  intro α W
  classical
  simp [M5.PrefixPartition.count]
