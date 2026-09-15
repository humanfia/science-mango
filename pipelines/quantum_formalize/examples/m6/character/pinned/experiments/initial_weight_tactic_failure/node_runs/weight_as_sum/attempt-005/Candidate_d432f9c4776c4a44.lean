import FrozenTarget_d432f9c4776c4a44
theorem M6.Character.weight_as_sum : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val
  intro m v
  classical
  unfold M6.Pinned.weight
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  generalize h : v i = a
  fin_cases a <;> norm_num [ZMod.val_zero, ZMod.val_one]
