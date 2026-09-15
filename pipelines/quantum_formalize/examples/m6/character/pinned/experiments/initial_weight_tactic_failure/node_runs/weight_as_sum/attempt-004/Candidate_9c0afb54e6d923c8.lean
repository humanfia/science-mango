import FrozenTarget_9c0afb54e6d923c8
theorem M6.Character.weight_as_sum : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val
  intro m v
  classical
  simp only [M6.Pinned.weight, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  fin_cases hx : v i <;> norm_num [ZMod.val_zero, ZMod.val_one]
