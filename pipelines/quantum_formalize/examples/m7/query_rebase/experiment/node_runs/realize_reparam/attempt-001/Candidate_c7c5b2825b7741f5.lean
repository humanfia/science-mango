import FrozenTarget_c7c5b2825b7741f5
theorem M7.QueryRebase.realize_reparam : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst bases moves x
  simpa only [M7.QueryRebase.rebase, M7.QueryRebase.reparam, M7.GlobalQuery.realize] using
    (M7.Action.act_compose N x.2 (moves x.1) (bases x.1)).symm
