import M7ActualPresentationAccepted
import M7GlobalQuery
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (i : Fin H), i ∈ M7.GlobalQuery.winningClasses q bases ↔ ∃ g : M7.Action.Record N, (i,g) ∈ M7.GlobalQuery.winners q bases
