import FrozenTarget_6fcdc6c52c76a3cf
theorem M6.Character.weight_as_sum : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val
  intro m v
  classical
  unfold M6.Pinned.weight
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  fin_cases h : v i <;> norm_num [ZMod.val_zero, ZMod.val_one]
