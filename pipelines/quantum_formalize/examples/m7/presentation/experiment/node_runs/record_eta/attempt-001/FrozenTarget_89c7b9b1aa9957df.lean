import M7Presentation
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (κ σ τ : Type) (a : M7.Presentation.Record κ σ τ), M7.Presentation.mk (M7.Presentation.outer a) (M7.Presentation.left a) (M7.Presentation.right a) = a
