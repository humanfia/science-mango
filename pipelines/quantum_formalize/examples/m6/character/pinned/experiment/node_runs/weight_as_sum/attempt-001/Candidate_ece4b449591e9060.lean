import FrozenTarget_ece4b449591e9060
theorem M6.Character.weight_as_sum : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val
  intro m v
  classical
  unfold M6.Pinned.weight
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  generalize hx : v i = x
  have hx01 : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx01 with rfl | rfl <;> norm_num [ZMod.val_zero, ZMod.val_one_eq_one_mod]
