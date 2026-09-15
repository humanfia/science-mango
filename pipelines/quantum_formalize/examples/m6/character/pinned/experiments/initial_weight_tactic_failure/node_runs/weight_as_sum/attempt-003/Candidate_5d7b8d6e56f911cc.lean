import FrozenTarget_5d7b8d6e56f911cc
theorem M6.Character.weight_as_sum : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val
  intro m v
  classical
  simp only [M6.Pinned.weight, Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro i hi
  generalize hx : v i = x
  fin_cases x <;> norm_num [ZMod.val_zero, ZMod.val_one]
