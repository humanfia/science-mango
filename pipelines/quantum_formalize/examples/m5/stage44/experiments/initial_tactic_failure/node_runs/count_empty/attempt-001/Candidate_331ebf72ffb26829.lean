import FrozenTarget_331ebf72ffb26829
theorem M5.PrefixPartition.count_empty : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ)
  intro α W
  classical
  simp [M5.PrefixPartition.count]
