import M6CSSDistance
import M6PinnedAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (LX LZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ LX ↔ J v ∈ LZ) → M6.Pinned.distance LX = M6.Pinned.distance LZ
