import FrozenTarget_3271f32ab1280c0e
theorem M7.DefaultQuery.winners_exact : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro N inst q base
  simpa [M7.DefaultQuery.winners, M7.ActualPresentation.selected,
    M7.Selection.feasibleSet, Finset.filter_eq_empty_iff] using
    (M7.Selection.selector_exact (M7.Action.Record N) q.objectives.length
      (Finset.univ : Finset (M7.Action.Record N))
      (fun g => M7.DefaultQuery.feasible q base (M7.Action.act g base))
      (fun g => M7.DefaultQuery.objective q (M7.Action.act g base)) q.order)
