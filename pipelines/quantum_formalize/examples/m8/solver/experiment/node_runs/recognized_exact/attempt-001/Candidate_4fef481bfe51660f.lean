import FrozenTarget_4fef481bfe51660f
theorem M8.Solver.recognized_exact : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c w hw hv
  constructor
  · rintro ⟨d, z, choice, k, hr⟩
    have hsig : M8.PhysicalBridge.signature c ≠ 1 := by
      intro hs
      simp [M8.Solver.run, M8.Solver.originalF_signature N c, hs] at hr
    refine ⟨hsig, (M8.Solver.discovery_span N c w hw hv).mp ?_⟩
    intro hn
    simp [M8.Solver.run, M8.Solver.originalF_signature N c, hsig, hn] at hr
  · rintro ⟨hsig, hspan⟩
    have hdiscover : M8.Discovery.discover c ≠ none :=
      (M8.Solver.discovery_span N c w hw hv).mpr hspan
    cases hd : M8.Discovery.discover c with
    | none => exact (hdiscover hd).elim
    | some choice =>
      have hsolve := M8.Solver.optimizer_present N c w hw hv hsig choice hd
      cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
      | none => exact (hsolve hs).elim
      | some result =>
        rcases result with ⟨d, v, k⟩
        refine ⟨d, M8.PhysicalBridge.undo (M8.Discovery.action choice) v, choice, k, ?_⟩
        simp [M8.Solver.run, M8.Solver.originalF_signature N c, hsig, hd, hs]
