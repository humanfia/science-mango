import FrozenTarget_992f8e663c984392
theorem M8.Solver.noLogical_exact : QuantumHarnessFrozenTarget := by
  intro N inst c w hw hc
  classical
  have hrun : M8.Solver.run c = M8.Solver.Outcome.noLogical (M8.PhysicalBridge.signature c) ↔ M8.PhysicalBridge.signature c = 1 := by
    by_cases hF : M8.PhysicalBridge.signature c = 1
    · simp [M8.Solver.run, M8.Solver.originalF_signature N c, hF]
    · cases hd : M8.Discovery.discover c with
      | none =>
          simp [M8.Solver.run, M8.Solver.originalF_signature N c, hF, hd]
      | some choice =>
          cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
          | none =>
              simp [M8.Solver.run, M8.Solver.originalF_signature N c, hF, hd, hs]
          | some result =>
              rcases result with ⟨d, v, k⟩
              simp [M8.Solver.run, M8.Solver.originalF_signature N c, hF, hd, hs]
  exact ⟨hrun, hrun.trans (M8.RawParameters.raw_noLogical N w c hw hc).1.symm⟩
