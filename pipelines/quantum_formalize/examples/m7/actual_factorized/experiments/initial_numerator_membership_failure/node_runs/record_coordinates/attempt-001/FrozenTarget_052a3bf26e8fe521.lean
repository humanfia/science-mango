import M7ActualFactorizedReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], Function.Bijective (@M7.ActualFactorized.toRecord N _)
