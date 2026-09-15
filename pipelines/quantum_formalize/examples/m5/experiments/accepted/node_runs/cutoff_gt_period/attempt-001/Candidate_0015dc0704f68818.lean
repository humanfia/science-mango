import FrozenTarget_0015dc0704f68818
theorem M5.cutoff_gt_period : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ), 2 ≤ w → 0 < T → T < M5.packingCutoff w T
  intro w T hw hT
  unfold M5.packingCutoff
  first
  | omega
  | nlinarith [Nat.sub_add_cancel (show 1 ≤ w by omega)]
