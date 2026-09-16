import FrozenTarget_af14132e35f40da4
theorem M8.Solver.output_gcd : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.outputF (M8.Solver.run c) = M8.PhysicalBridge.signature c
  intro N inst c
  classical
  unfold M8.Solver.run
  split
  · exact M8.Solver.originalF_signature N c
  · split
    · exact M8.Solver.originalF_signature N c
    · split <;> exact M8.Solver.originalF_signature N c
