import M7ActualPresentationAccepted
import M7DefaultQuery
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), q.objectives = [] → M7.DefaultQuery.winners q base = M7.Selection.feasibleSet Finset.univ (fun g : M7.Action.Record N => M7.DefaultQuery.feasible q base (M7.Action.act g base))
