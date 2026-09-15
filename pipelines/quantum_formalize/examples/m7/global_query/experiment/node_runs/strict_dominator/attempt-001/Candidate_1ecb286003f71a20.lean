import FrozenTarget_1ecb286003f71a20
theorem M7.GlobalQuery.strict_dominator : QuantumHarnessFrozenTarget := by
  intro H N inst q bases x hx hn
  classical
  exact M7.Selection.selector_strict_dominator
    (M7.GlobalQuery.Index H N) q.objectives.length Finset.univ
    (M7.GlobalQuery.feasible q bases) (M7.GlobalQuery.objective q bases)
    q.order x (Finset.mem_univ x) hx hn
