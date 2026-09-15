import M7Presentation
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (κ σ τ X Y : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y) (m : ℕ) (feasible : X × Y → Prop) (objective : X × Y → Fin m → ℤ) (mode : M7.Selection.Mode) (a b : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.domain K S T → b ∈ M7.Presentation.domain K S T → M7.Presentation.realize l r a = M7.Presentation.realize l r b → (a ∈ M7.Presentation.selected K S T l r feasible objective mode ↔ b ∈ M7.Presentation.selected K S T l r feasible objective mode)
