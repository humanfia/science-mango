import FrozenTarget_3768ac090dc8e644
theorem M5.PrefixPartition.count_partition : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a])
  intro α _ _ W m p hW hp
  classical
  have hword : ∀ q ∈ W, (if p.IsPrefix q then (1 : ℤ) else 0) = ∑ a : α, if (p ++ [a]).IsPrefix q then (1 : ℤ) else 0 := by
    intro q hq
    have hlen : p.length < q.length := by simpa only [hW q hq] using hp
    have he (a : α) := M5.PrefixPartition.prefix_next α p q a hlen
    simp only [he]
    by_cases hprefix : p.IsPrefix q
    · simp [hprefix, eq_comm]
    · simp [hprefix]
  have hsum := Finset.sum_congr rfl hword
  rw [Finset.sum_comm] at hsum
  simpa [M5.PrefixPartition.count, Finset.card_eq_sum_ones, Finset.sum_filter] using hsum
