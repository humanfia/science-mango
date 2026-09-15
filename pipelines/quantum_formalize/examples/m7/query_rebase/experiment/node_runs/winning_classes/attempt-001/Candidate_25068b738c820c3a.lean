import FrozenTarget_25068b738c820c3a
theorem M7.QueryRebase.winning_classes : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases moves
  apply Finset.ext
  intro i
  rw [M7.GlobalQuery.winning_classes H N q (M7.QueryRebase.rebase bases moves) i,
    M7.GlobalQuery.winning_classes H N q bases i]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(M7.QueryRebase.reparam moves (i, g)).2, ?_⟩
    exact (M7.QueryRebase.winners_reparam H N q bases moves (i, g)).mp hg
  · rintro ⟨g, hg⟩
    refine ⟨(M7.QueryRebase.undo moves (i, g)).2, ?_⟩
    change M7.QueryRebase.undo moves (i, g) ∈ M7.GlobalQuery.winners q (M7.QueryRebase.rebase bases moves)
    apply (M7.QueryRebase.winners_reparam H N q bases moves (M7.QueryRebase.undo moves (i, g))).mpr
    rw [(M7.QueryRebase.reparameterization H N moves).2.1 (i, g)]
    exact hg
