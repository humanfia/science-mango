import M7ActualPresentation
import M7PresentationAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M7.Presentation.domain (Finset.univ : Finset (M7.ActualPresentation.Outer N)) (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin N)) = (Finset.univ : Finset (M7.ActualPresentation.Encoded N))
