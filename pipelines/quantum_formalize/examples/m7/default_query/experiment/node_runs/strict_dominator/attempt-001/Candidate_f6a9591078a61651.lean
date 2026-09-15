import FrozenTarget_f6a9591078a61651
theorem M7.DefaultQuery.strict_dominator : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst q base g hg hnot
  classical
  exact M7.Selection.selector_strict_dominator
    (M7.Action.Record N) q.objectives.length Finset.univ
    (fun h => M7.DefaultQuery.feasible q base (M7.Action.act h base))
    (fun h => M7.DefaultQuery.objective q (M7.Action.act h base))
    q.order g (Finset.mem_univ g) hg hnot
