import FrozenTarget_8765216f0eef0e82
theorem M7.FinalReplay.physical_labels : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q hw hwN c hc i
  have hp := (M7.FinalReplay.parts N w q c).mp hc
  have hE : M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q) := by
    apply M7.QuerySectors.effective_valid
    exact hp.1
  have hg := (M7.GeneratedFamily.family_good N w (M7.QuerySectors.effective N q) hw hwN hE i).1
  have ha := M7.GeneratedFamily.family_anchored N w (M7.QuerySectors.effective N q) hw hwN hE i
  have hl := hp.2.2.2.2.1 i
  apply M7.LabelReplay.checked_physical_answer N w (M7.FinalSelector.family N w q i) (c.labels i)
  all_goals
    simp only [M7.FinalSelector.family, M7.PrefixOrbit.ClassValid] at *
    aesop
