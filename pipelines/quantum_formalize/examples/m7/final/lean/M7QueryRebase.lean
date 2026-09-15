import M7GlobalQuery
namespace M7.QueryRebase
noncomputable def rebase {H N : ℕ} [NeZero N] (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) : M7.GlobalQuery.Family H N := fun i => M7.Action.act (moves i) (bases i)
noncomputable def reparam {H N : ℕ} [NeZero N] (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N) : M7.GlobalQuery.Index H N := (x.1, M7.Action.compose x.2 (moves x.1))
noncomputable def undo {H N : ℕ} [NeZero N] (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N) : M7.GlobalQuery.Index H N := (x.1, M7.Action.compose x.2 (M7.Action.inverse (moves x.1)))
end M7.QueryRebase
