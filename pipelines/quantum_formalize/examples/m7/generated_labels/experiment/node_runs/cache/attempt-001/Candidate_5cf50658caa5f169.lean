import FrozenTarget_5cf50658caa5f169
theorem M7.GeneratedLabels.cache : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE i g
  have hvalid := (M7.GeneratedFamily.family_good N w E hw hwN hE i).1
  obtain ⟨hleft, hright⟩ := M7.GeneratedFamily.family_anchored N w E hw hwN hE i
  apply M7.QualityTable.cache_action N w (M7.GeneratedFamily.family N w E i) ?_ ?_ hleft hright ?_ g
  all_goals aesop [M7.PrefixOrbit.ClassValid]
