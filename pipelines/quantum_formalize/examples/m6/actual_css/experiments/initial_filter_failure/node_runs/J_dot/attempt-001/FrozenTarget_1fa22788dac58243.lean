import M6ActualCSS
import M6ActualCSSDependencies


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (v w : M6.Pinned.Vector (2*N)), M6.Character.dot (M6.Flatten.J N v) (M6.Flatten.J N w) = M6.Character.dot v w
