import M7ActualPresentationAccepted
import M7DefaultQuery
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (∀ g : M7.Action.Record N, g ∈ M7.DefaultQuery.winners q base ↔ M7.DefaultQuery.feasible q base (M7.Action.act g base) ∧ ∀ h : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act h base) → ¬ M7.Selection.better q.order (M7.DefaultQuery.objective q (M7.Action.act h base)) (M7.DefaultQuery.objective q (M7.Action.act g base))) ∧ (M7.DefaultQuery.winners q base = ∅ ↔ ¬ ∃ g : M7.Action.Record N, M7.DefaultQuery.feasible q base (M7.Action.act g base))
