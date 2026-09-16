import FrozenTarget_108099ddc3ac41dd
theorem M8.Solver.output_gcd : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.outputF (M8.Solver.run c) = M8.PhysicalBridge.signature c
  intro N inst c
  classical
  by_cases h : M8.Solver.originalF c = 1
  · simpa [M8.Solver.run, h, M8.Solver.outputF] using M8.Solver.originalF_signature N c
  · cases hd : M8.Discovery.discover c with
    | none =>
        simpa [M8.Solver.run, h, hd, M8.Solver.outputF] using M8.Solver.originalF_signature N c
    | some choice =>
        cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
        | none =>
            simpa [M8.Solver.run, h, hd, hs, M8.Solver.outputF] using M8.Solver.originalF_signature N c
        | some result =>
            rcases result with ⟨d, v, k⟩
            simpa [M8.Solver.run, h, hd, hs, M8.Solver.outputF] using M8.Solver.originalF_signature N c
