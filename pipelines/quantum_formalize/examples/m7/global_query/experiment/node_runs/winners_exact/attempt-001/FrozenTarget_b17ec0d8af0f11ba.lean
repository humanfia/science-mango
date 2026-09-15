import M7ActualPresentationAccepted
import M7GlobalQuery
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (∀ x : M7.GlobalQuery.Index H N, x ∈ M7.GlobalQuery.winners q bases ↔ M7.GlobalQuery.feasible q bases x ∧ ∀ y : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases y → ¬ M7.Selection.better q.order (M7.GlobalQuery.objective q bases y) (M7.GlobalQuery.objective q bases x)) ∧ (M7.GlobalQuery.winners q bases = ∅ ↔ ¬ ∃ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases x)
