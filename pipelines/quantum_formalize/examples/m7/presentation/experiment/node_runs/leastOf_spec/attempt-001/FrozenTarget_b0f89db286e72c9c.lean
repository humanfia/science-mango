import M7Presentation
import M7SelectionAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α : Type) [LinearOrder α] (T : Finset α), (∀ x, M7.Presentation.leastOf T = some x ↔ x ∈ T ∧ ∀ y ∈ T, x ≤ y) ∧ (M7.Presentation.leastOf T = none ↔ T = ∅)
