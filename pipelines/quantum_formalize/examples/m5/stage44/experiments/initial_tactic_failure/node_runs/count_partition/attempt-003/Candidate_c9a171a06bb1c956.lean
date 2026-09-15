import FrozenTarget_c9a171a06bb1c956
theorem M5.PrefixPartition.count_partition : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a])
  intro α _ _ W m p hW hp
  classical
  suffices hc : (W.filter (fun q => p.IsPrefix q)).card = ∑ a : α, (W.filter (fun q => (p ++ [a]).IsPrefix q)).card by
    simpa only [M5.PrefixPartition.count, Nat.cast_sum] using congrArg (fun n : ℕ => (n : ℤ)) hc
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have hlen : p.length < q.length := by rw [hW q hq]; exact hp
  simp only [M5.PrefixPartition.prefix_next α p q _ hlen]
  by_cases hprefix : p.IsPrefix q
  · simp only [hprefix, true_and, if_true, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [hprefix, false_and, if_false, Finset.sum_const_zero]
