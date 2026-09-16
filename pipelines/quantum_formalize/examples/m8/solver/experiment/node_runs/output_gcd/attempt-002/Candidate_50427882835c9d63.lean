import FrozenTarget_50427882835c9d63
theorem M8.Solver.output_gcd : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.outputF (M8.Solver.run c) = M8.PhysicalBridge.signature c
  intro N inst c
  classical
  by_cases h : M8.Solver.originalF c = 1
  · simpa only [M8.Solver.run, h, if_pos, M8.Solver.outputF] using M8.Solver.originalF_signature N c
  · cases hd : M8.Discovery.discover c with
    | none =>
        simpa only [M8.Solver.run, h, if_neg, hd, M8.Solver.outputF] using M8.Solver.originalF_signature N c
    | some choice =>
        cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
        | none =>
            simpa only [M8.Solver.run, h, if_neg, hd, hs, M8.Solver.outputF] using M8.Solver.originalF_signature N c
        | some result =>
            rcases result with ⟨d, v, k⟩
            simpa only [M8.Solver.run, h, if_neg, hd, hs, M8.Solver.outputF] using M8.Solver.originalF_signature N c
