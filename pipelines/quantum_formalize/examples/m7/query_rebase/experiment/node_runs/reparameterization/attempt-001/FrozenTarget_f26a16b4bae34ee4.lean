import M7ActionAccepted
import M7GlobalQueryAccepted
import M7QueryRebase


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (moves : Fin H → M7.Action.Record N), (∀ x : M7.GlobalQuery.Index H N, M7.QueryRebase.undo moves (M7.QueryRebase.reparam moves x) = x) ∧ (∀ x : M7.GlobalQuery.Index H N, M7.QueryRebase.reparam moves (M7.QueryRebase.undo moves x) = x) ∧ Function.Bijective (M7.QueryRebase.reparam moves)
