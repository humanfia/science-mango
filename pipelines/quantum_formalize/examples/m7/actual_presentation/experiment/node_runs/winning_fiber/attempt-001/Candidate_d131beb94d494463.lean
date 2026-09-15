import FrozenTarget_d131beb94d494463
theorem M7.ActualPresentation.winning_fiber : QuantumHarnessFrozenTarget := by
  intro N inst c m feasible objective mode g h heq
  classical
  unfold M7.ActualPresentation.selected
  rw [(M7.Selection.selector_exact _ _ _ _ _ _).1 g,
      (M7.Selection.selector_exact _ _ _ _ _ _).1 h]
  simp only [Finset.mem_univ, true_and, heq]
