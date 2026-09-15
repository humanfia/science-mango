import FrozenTarget_f26a16b4bae34ee4
theorem M7.QueryRebase.reparameterization : QuantumHarnessFrozenTarget := by
  intro H N inst moves
  have hundo : ∀ x : M7.GlobalQuery.Index H N,
      M7.QueryRebase.undo moves (M7.QueryRebase.reparam moves x) = x := by
    rintro ⟨i, g⟩
    simp [M7.QueryRebase.undo, M7.QueryRebase.reparam,
      M7.Action.associative, M7.Action.right_inverse,
      M7.Action.left_inverse, M7.Action.right_identity]
  have hreparam : ∀ x : M7.GlobalQuery.Index H N,
      M7.QueryRebase.reparam moves (M7.QueryRebase.undo moves x) = x := by
    rintro ⟨i, g⟩
    simp [M7.QueryRebase.undo, M7.QueryRebase.reparam,
      M7.Action.associative, M7.Action.right_inverse,
      M7.Action.left_inverse, M7.Action.right_identity]
  refine ⟨hundo, hreparam, ?_, ?_⟩
  · intro x y h
    calc
      x = M7.QueryRebase.undo moves (M7.QueryRebase.reparam moves x) := (hundo x).symm
      _ = M7.QueryRebase.undo moves (M7.QueryRebase.reparam moves y) := congrArg (M7.QueryRebase.undo moves) h
      _ = y := hundo y
  · intro y
    exact ⟨M7.QueryRebase.undo moves y, hreparam y⟩
