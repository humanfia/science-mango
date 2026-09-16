import FrozenTarget_c27afaac1754aefd
theorem M8.WholeResources.projection : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c
  change (M8.WholeResources.run c).outcome = M8.Solver.run c
  by_cases h : M8.Solver.originalF c = 1
  · simp [M8.WholeResources.run, M8.Solver.run, h]
  · simp only [M8.WholeResources.run, M8.Solver.run, h, if_false,
      M8.DiscoveryResources.projection]
    cases hd : M8.Discovery.discover c with
    | none => simp [hd]
    | some choice =>
      simp only [hd]
      cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
      | none => simp [hs]
      | some result =>
        rcases result with ⟨d, v, k⟩
        simp [hs]
