import M7ActualPresentation
import M7PresentationAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g h : M7.Action.Record N), M7.Action.act g c = M7.Action.act h c → (g ∈ M7.ActualPresentation.selected c feasible objective mode ↔ h ∈ M7.ActualPresentation.selected c feasible objective mode)
