import FrozenTarget_850c87f72887a85b
theorem M7.FinalSelector.index_feasible : QuantumHarnessFrozenTarget := by
  intro N w inst q hw hwN hq x
  have hb : M7.PrefixOrbit.ClassValid w (M7.FinalSelector.family N w q x.1) :=
    (M7.GeneratedFamily.family_good N w (M7.QuerySectors.effective N q) hw hwN
      (M7.QuerySectors.effective_valid N q hq) x.1).1
  have hc : M7.PrefixOrbit.ClassValid w
      (M7.Action.act x.2 (M7.FinalSelector.family N w q x.1)) := by
    first
    | simpa only [M7.PrefixOrbit.class_action] using hb
    | solve_by_elim [M7.PrefixOrbit.class_action]
  simp only [M7.GlobalQuery.feasible, M7.FinalSelector.RawFeasible,
    M7.FinalSelector.realize, M7.GlobalQuery.realize,
    M7.DefaultQuery.feasible, M7.Action.act_identity,
    M7.QueryRebase.sector_base, hc, true_and, and_true]
