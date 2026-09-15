import FrozenTarget_4b4adeea5246aa0c
theorem M7.GenerationReplay.step_exact : QuantumHarnessFrozenTarget := by
    classical
    intro N inst w E bases e
    change M7.GenerationReplay.stepPass w E bases e = true ↔ _
    constructor
    · intro h
      simp only [M7.GenerationReplay.stepPass, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨hpos, hcheck⟩, hdepth, hleaf, hrep, haction, hleafSig, hrepSig, hstab⟩
      have hpath := M7.DescentTrace.check_unique
        (M7.CompactGeneration.residual w E bases) [] e.path hcheck
      rw [hdepth] at hpath
      refine ⟨hpos, ?_⟩
      cases e
      dsimp only at *
      simp_all [M7.CompactGeneration.emission, M7.DescentTrace.endpoint_recover]
    · rintro ⟨hpos, rfl⟩
      simp [M7.GenerationReplay.stepPass, M7.CompactGeneration.emission,
        M7.DescentTrace.trace_length, M7.DescentTrace.check_trace,
        M7.DescentTrace.endpoint_recover, hpos]
