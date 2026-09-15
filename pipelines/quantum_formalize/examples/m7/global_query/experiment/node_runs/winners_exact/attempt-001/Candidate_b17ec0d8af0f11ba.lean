import FrozenTarget_b17ec0d8af0f11ba
theorem M7.GlobalQuery.winners_exact : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases
  simpa [M7.GlobalQuery.winners, M7.Selection.feasibleSet,
    Finset.filter_eq_empty_iff, not_exists] using
    (M7.Selection.selector_exact (M7.GlobalQuery.Index H N)
      q.objectives.length Finset.univ (M7.GlobalQuery.feasible q bases)
      (M7.GlobalQuery.objective q bases) q.order)
