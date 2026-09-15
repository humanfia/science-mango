import FrozenTarget_89a4f3e856efdd6d
theorem M7.Selection.win_sound_complete : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop) (x : α), x ∈ M7.Selection.winners T feasible R ↔ x ∈ T ∧ feasible x ∧ ∀ y ∈ T, feasible y → ¬ R y x
  intro α T feasible R x
  classical
  rw [M7.Selection.win_membership]
  simp [M7.Selection.win, M7.Selection.feasibleSet, not_exists, and_assoc, and_left_comm, and_comm]
