import M7ActualPresentation
import M7PresentationAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a : M7.ActualPresentation.Encoded N), M7.ActualPresentation.encode (M7.ActualPresentation.decode a) = a
