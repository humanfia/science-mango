import M7ActualPresentationAccepted
import M7DefaultQuery
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (base : M7.Action.Recipe N), (∀ g ∈ M7.DefaultQuery.winners q base, ∃! h : M7.Action.Record N, M7.DefaultQuery.present q base h ∧ M7.Action.act h base = M7.Action.act g base ) ∧ (∀ g : M7.Action.Record N, M7.DefaultQuery.present q base g → g ∈ M7.DefaultQuery.winners q base ∧ ∀ h : M7.Action.Record N, M7.Action.act h base = M7.Action.act g base → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h)
