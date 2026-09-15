import M6CSSDistance
import M6PinnedAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (v : M6.CSS.Vector m), M6.CSS.weight (v, 0) = M6.Pinned.weight v ∧ M6.CSS.weight (0, v) = M6.Pinned.weight v
