import FrozenTarget_05ea9a876375c3e0
theorem M8.Solver.noLogical_exact : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c w hw hc
  have h : M8.Solver.run c = M8.Solver.Outcome.noLogical (M8.PhysicalBridge.signature c) ↔ M8.PhysicalBridge.signature c = 1 := by
    unfold M8.Solver.run
    rw [M8.Solver.originalF_signature N c]
    by_cases hF : M8.PhysicalBridge.signature c = 1
    · simp [hF]
    · simp only [hF, if_false]
      cases hd : M8.Discovery.discover c with
      | none => simp [hF]
      | some choice =>
        cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
        | none => simp [hF]
        | some result =>
          rcases result with ⟨d, v, k⟩
          simp [hF]
  exact ⟨h, h.trans (M8.RawParameters.raw_noLogical N w c hw hc).1.symm⟩
