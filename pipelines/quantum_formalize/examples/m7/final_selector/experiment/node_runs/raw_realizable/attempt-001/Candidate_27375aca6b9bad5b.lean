import FrozenTarget_27375aca6b9bad5b
theorem M7.FinalSelector.raw_realizable : QuantumHarnessFrozenTarget := by
  intro N w inst q hw hwN hq c hc
  have hv : M7.PrefixOrbit.ClassValid w c := hc.1
  have hs : M7.DefaultQuery.sectorTest q c c := by
    unfold M7.FinalSelector.RawFeasible M7.DefaultQuery.feasible at hc
    tauto
  have hall : ∀ d : M7.Action.Recipe N,
      M7.DefaultQuery.allows q (M7.DefaultQuery.signature d) →
        M7.RecipeSignature.signature d ∈ M7.QuerySectors.effective N q := by
    intro d hd
    exact (M7.QuerySectors.signature_allowed N q d).mpr hd
  have horbit : ∃ g : M7.Action.Record N,
      M7.RecipeSignature.signature (M7.Action.act g c) ∈ M7.QuerySectors.effective N q := by
    unfold M7.DefaultQuery.sectorTest at hs
    split at hs
    all_goals
      first
      | obtain ⟨g, hg⟩ := hs
        exact ⟨g, hall _ hg⟩
      | refine ⟨M7.Action.identity N, ?_⟩
        rw [M7.Action.act_identity]
        exact hall c hs
  obtain ⟨i, g, hg⟩ :=
    (M7.GeneratedFamily.family_complete N w (M7.QuerySectors.effective N q)
      hw hwN (M7.QuerySectors.effective_valid N q hq) c).mpr ⟨hv, horbit⟩
  exact ⟨(i, g), hg⟩
