import FrozenTarget_cc4d53c5942213f5
theorem M6.Physical.conv_comm : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Physical.conv N a b = M6.Physical.conv N b a
  intro N inst a b
  classical
  funext i
  unfold M6.Physical.conv
  refine Finset.sum_bij (fun r _ => i - r) ?_ ?_ ?_ ?_
  · intro r hr
    exact Finset.mem_univ _
  · intro r hr s hs h
    simpa only [sub_sub_cancel] using congrArg (fun t => i - t) h
  · intro r hr
    exact ⟨i - r, Finset.mem_univ _, sub_sub_cancel i r⟩
  · intro r hr
    simp only [sub_sub_cancel, mul_comm]
