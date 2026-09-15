import M6CSSDistance
import M6PinnedAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (p : M6.CSS.Pauli m), M6.Pinned.weight p.1 ≤ M6.CSS.weight p ∧ M6.Pinned.weight p.2 ≤ M6.CSS.weight p
