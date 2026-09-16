import FrozenTarget_5856e94479b0cc84
theorem M8.BankLayout.actual_workspace_fits : QuantumHarnessFrozenTarget := by
  intro N inst a b h
  change M6.Transfer.solveStorage (M6.ActualTransfer.span a b) N (M6.EuclidStorage.actualPreprocessStorage N) ≤ M6.Transfer.solveStorage (M8.Cutoff.limit N) N (M6.EuclidStorage.actualPreprocessStorage N)
  exact M8.BankLayout.workspace_monotone (M6.ActualTransfer.span a b) (M8.Cutoff.limit N) N (M6.EuclidStorage.actualPreprocessStorage N) h
