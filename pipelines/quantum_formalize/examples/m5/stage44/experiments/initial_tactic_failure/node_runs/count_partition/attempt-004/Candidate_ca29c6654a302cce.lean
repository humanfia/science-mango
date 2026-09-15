import FrozenTarget_ca29c6654a302cce
theorem M5.PrefixPartition.count_partition : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a])
  intro α _ _ W m p hW hp
  classical
  have hc : (W.filter (fun q => p.IsPrefix q)).card =
      ∑ a : α, (W.filter (fun q => (p ++ [a]).IsPrefix q)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    have h : p.length < q.length := by
      rw [hW q hq]
      exact hp
    have hn : ∀ a : α, (p ++ [a]).IsPrefix q ↔
        p.IsPrefix q ∧ q.get ⟨p.length, h⟩ = a :=
      fun a => M5.PrefixPartition.prefix_next α p q a h
    simp only [hn]
    by_cases hpq : p.IsPrefix q
    · simp [hpq]
    · simp [hpq]
  change ((W.filter (fun q => p.IsPrefix q)).card : ℤ) =
    ∑ a : α, ((W.filter (fun q => (p ++ [a]).IsPrefix q)).card : ℤ)
  exact_mod_cast hc
