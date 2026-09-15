import FrozenTarget_4863c6529166be2c
theorem M7.GeneratedLabels.pointwise : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE i
  have hgood := (M7.GeneratedFamily.family_good N w E hw hwN hE i).1
  have hanchored := M7.GeneratedFamily.family_anchored N w E hw hwN hE i
  apply M7.ClosedSolve.closed_pointwise N w (M7.GeneratedFamily.family N w E i)
  all_goals
    simp_all [M7.PrefixOrbit.ClassValid]
