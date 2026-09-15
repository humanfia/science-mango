import FrozenTarget_a8470918b1c1f58f
theorem M7.Selection.win_membership : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop) (x : α), x ∈ M7.Selection.winners T feasible R ↔ M7.Selection.win T feasible R x
  intro α T feasible R x
  classical
  simp [M7.Selection.winners, M7.Selection.win, M7.Selection.feasibleSet, and_assoc, and_left_comm, and_comm]
