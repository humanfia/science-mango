import M7ActualPresentation
import M7PresentationAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N), M7.ActualPresentation.decode (M7.ActualPresentation.encode g) = g
