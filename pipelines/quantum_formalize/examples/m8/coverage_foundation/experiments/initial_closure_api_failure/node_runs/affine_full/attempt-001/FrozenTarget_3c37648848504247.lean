import M8CoverageFoundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (A : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), M8.CoverageFoundation.FullDirection (A.image (M7.Action.affine u s)) ↔ M8.CoverageFoundation.FullDirection A
