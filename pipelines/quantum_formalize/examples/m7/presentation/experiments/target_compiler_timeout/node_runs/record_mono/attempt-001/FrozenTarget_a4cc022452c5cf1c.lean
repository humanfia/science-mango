import M7Presentation
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (k : κ) (s s1 : σ) (t t1 : τ), s ≤ s1 → t ≤ t1 → M7.Presentation.mk k s t ≤ M7.Presentation.mk k s1 t1
