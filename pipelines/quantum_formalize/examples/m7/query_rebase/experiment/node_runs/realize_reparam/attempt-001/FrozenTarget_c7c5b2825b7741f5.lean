import M7ActionAccepted
import M7GlobalQueryAccepted
import M7QueryRebase


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (bases : M7.GlobalQuery.Family H N) (moves : Fin H → M7.Action.Record N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.realize (M7.QueryRebase.rebase bases moves) x = M7.GlobalQuery.realize bases (M7.QueryRebase.reparam moves x)
