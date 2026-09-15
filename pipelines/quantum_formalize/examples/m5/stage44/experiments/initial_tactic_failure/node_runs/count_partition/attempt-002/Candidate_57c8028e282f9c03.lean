import FrozenTarget_57c8028e282f9c03
theorem M5.PrefixPartition.count_partition : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a])
  intro α _ _ W m p hW hp
  classical
  suffices h : (∑ q ∈ W, if p.IsPrefix q then (1 : ℤ) else 0) =
      ∑ a : α, ∑ q ∈ W, if (p ++ [a]).IsPrefix q then (1 : ℤ) else 0 by
    simpa [M5.PrefixPartition.count, Finset.card_eq_sum_ones,
      Finset.sum_filter, List.prefix_iff_eq_take, eq_comm] using h
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have hl : p.length < q.length := by simpa [hW q hq] using hp
  simp only [M5.PrefixPartition.prefix_next α p q _ hl]
  by_cases hprefix : p.IsPrefix q
  · simp [hprefix, eq_comm]
  · simp [hprefix]
