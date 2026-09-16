import M8DiscoveryResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)), M8.DiscoveryResources.memberCharge A ≤ 4*N*(N+1) ∧ M8.DiscoveryResources.spanCharge A ≤ 16*N*(N+1)^2
