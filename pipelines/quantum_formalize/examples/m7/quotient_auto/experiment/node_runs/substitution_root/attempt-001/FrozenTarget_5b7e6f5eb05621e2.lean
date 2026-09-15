import M7QuotientAuto


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.QuotientAuto.substitution u (M7.CyclicSubstitution.rho N) = M7.CyclicSubstitution.point u
