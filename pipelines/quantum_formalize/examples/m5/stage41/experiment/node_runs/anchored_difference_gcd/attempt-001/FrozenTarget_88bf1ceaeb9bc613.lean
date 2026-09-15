import M5Translation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (S U : Finset (ZMod N)), 0 ∈ S → 0 ∈ U → M5.Translation.differenceGcd S U = M5.Connectivity.supportGcd N (M5.Translation.natSupport S) (M5.Translation.natSupport U)
