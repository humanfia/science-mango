import M6CSSDistance
import M6PinnedAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (M6.CSS.quantumDistance BX CX BZ CZ = none ↔ M6.CSS.logicalPaulis BX CX BZ CZ = ∅) ∧ ∀ d : ℕ, (M6.CSS.quantumDistance BX CX BZ CZ = some d ↔ (∃ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, M6.CSS.weight p = d) ∧ ∀ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, d ≤ M6.CSS.weight p)
