import M7QuotientAuto


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (r : ZMod 2), M7.QuotientAuto.substitution u ((AdjoinRoot.of (M6.Cyclic.modulus N)) r) = (AdjoinRoot.of (M6.Cyclic.modulus N)) r
