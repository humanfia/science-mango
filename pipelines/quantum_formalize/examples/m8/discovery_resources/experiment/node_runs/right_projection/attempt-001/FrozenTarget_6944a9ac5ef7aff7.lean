import M8DiscoveryResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t a : Fin N), (M8.DiscoveryResources.rightRun c e t a).selected.map Prod.snd = M8.Discovery.atRight c e t a
