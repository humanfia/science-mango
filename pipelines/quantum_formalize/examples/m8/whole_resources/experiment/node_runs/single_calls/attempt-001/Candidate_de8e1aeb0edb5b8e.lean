import FrozenTarget_de8e1aeb0edb5b8e
theorem M8.WholeResources.single_calls : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c
  change (M8.WholeResources.run c).discoveryCalls ≤ 1 ∧ (M8.WholeResources.run c).optimizerCalls ≤ (M8.WholeResources.run c).discoveryCalls
  by_cases h : M8.Solver.originalF c = 1
  · simp [M8.WholeResources.run, h]
  · cases hs : (M8.DiscoveryResources.run c).selected.map Prod.snd with
    | none => simp [M8.WholeResources.run, h, hs]
    | some choice =>
      cases ho : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
      | none => simp [M8.WholeResources.run, h, hs, ho]
      | some result =>
        rcases result with ⟨d, v, k⟩
        simp [M8.WholeResources.run, h, hs, ho]
