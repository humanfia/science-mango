import FrozenTarget_9cdfc55989a89b27
theorem M6.ActualTransfer.shifted_scan_exact : QuantumHarnessFrozenTarget := by
  intro N inst a b P
  classical
  simp only [M6.ActualTransfer.shiftedScan, M6.Pinned.firstPositive,
    M6.ActualTransfer.shifted_coefficient_exact]
