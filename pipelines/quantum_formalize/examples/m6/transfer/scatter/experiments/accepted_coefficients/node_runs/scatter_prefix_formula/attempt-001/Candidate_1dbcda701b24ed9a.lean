import FrozenTarget_1dbcda701b24ed9a
theorem M6.Transfer.scatter_prefix_formula : QuantumHarnessFrozenTarget := by
  classical
  intro R N W input initial l addr
  induction l generalizing initial with
  | nil => simp
  | cons e l ih =>
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      cases h : M6.Transfer.eventDestination e with
      | none =>
          simp [M6.Transfer.scatterUpdate, h]
      | some a =>
          by_cases ha : a = addr
          · subst a
            simp [M6.Transfer.scatterUpdate, h, add_assoc]
          · simp [M6.Transfer.scatterUpdate, h, Function.update_apply, ha, Ne.symm ha]
