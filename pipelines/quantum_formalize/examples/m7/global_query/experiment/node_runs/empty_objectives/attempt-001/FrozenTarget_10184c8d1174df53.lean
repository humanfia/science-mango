import M7ActualPresentationAccepted
import M7GlobalQuery
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), q.objectives = [] → M7.GlobalQuery.winners q bases = M7.Selection.feasibleSet Finset.univ (M7.GlobalQuery.feasible q bases)
