import FrozenTarget_730223e8a04d84a9
theorem M7.FinalSelector.raw_realizable : QuantumHarnessFrozenTarget := by
  intro N w inst q hw hwN hq c hc
  classical
  have hv : M7.PrefixOrbit.ClassValid w c := by
    unfold M7.FinalSelector.RawFeasible at hc
    tauto
  have hs : M7.DefaultQuery.sectorTest q c c := by
    unfold M7.FinalSelector.RawFeasible at hc
    tauto
  have ho : ∃ g : M7.Action.Record N,
      M7.RecipeSignature.signature (M7.Action.act g c) ∈ M7.QuerySectors.effective N q := by
    unfold M7.DefaultQuery.sectorTest at hs
    split at hs
    all_goals
      first
      | obtain ⟨g, hg⟩ := hs
        exact ⟨g, (M7.QuerySectors.signature_allowed N q (M7.Action.act g c)).mpr hg⟩
      | refine ⟨M7.Action.identity N, ?_⟩
        rw [M7.Action.act_identity N c]
        exact (M7.QuerySectors.signature_allowed N q c).mpr hs
  obtain ⟨i, g, hg⟩ :=
    (M7.GeneratedFamily.family_complete N w (M7.QuerySectors.effective N q)
      hw hwN (M7.QuerySectors.effective_valid N q hq) c).mpr ⟨hv, ho⟩
  exact ⟨(i, g), hg⟩
