import M7Presentation
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.candidates K L R → M7.Presentation.valid K L R a
