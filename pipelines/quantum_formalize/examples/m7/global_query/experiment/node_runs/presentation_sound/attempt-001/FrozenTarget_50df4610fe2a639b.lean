import M7ActualPresentationAccepted
import M7GlobalQuery
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.present q bases x → x ∈ M7.GlobalQuery.winners q bases ∧ ∀ g : M7.Action.Record N, M7.Action.act g (bases x.1) = M7.GlobalQuery.realize bases x → M7.ActualPresentation.encode x.2 ≤ M7.ActualPresentation.encode g
