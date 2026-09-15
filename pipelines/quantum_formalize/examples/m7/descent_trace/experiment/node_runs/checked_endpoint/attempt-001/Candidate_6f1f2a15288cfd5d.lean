import FrozenTarget_6f1f2a15288cfd5d
theorem M7.DescentTrace.checked_endpoint : QuantumHarnessFrozenTarget := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).1 = true → M7.DescentTrace.endpoint p ss = M5.BinaryRecovery.recover c p ss.length
  intro c p ss h
  exact (congrArg (M7.DescentTrace.endpoint p) (M7.DescentTrace.check_unique c p ss h)).trans (M7.DescentTrace.endpoint_recover c p ss.length)
