import M6CSSDistance
import M6PinnedAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (p : M6.CSS.Pauli m), p ∈ M6.CSS.logicalPaulis BX CX BZ CZ ↔ p.1 ∈ CX ∧ p.2 ∈ CZ ∧ (p.1 ∈ M6.CSS.logical BX CX ∨ p.2 ∈ M6.CSS.logical BZ CZ)
