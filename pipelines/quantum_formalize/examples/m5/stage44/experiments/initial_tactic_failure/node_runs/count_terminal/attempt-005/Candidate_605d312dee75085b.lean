import FrozenTarget_605d312dee75085b
theorem M5.PrefixPartition.count_terminal : QuantumHarnessFrozenTarget := by
  intro α inst W m p hW hp
  classical
  have ht : ∀ q ∈ W, q.take p.length = q := by
    intro q hq
    rw [hp, ← hW q hq, List.take_length]
  have hf : W.filter (fun q => p <+: q) = W.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q hq
    simp [List.prefix_iff_eq_take, ht q hq, eq_comm]
  have hg : W.filter (fun q => q.take p.length = p) = W.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q hq
    rw [ht q hq]
  have hh : W.filter (fun q => p = q.take p.length) = W.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q hq
    simp [ht q hq, eq_comm]
  simp [M5.PrefixPartition.count, hf, hg, hh]
