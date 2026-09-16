import M8DiscoveryResources

theorem M8.DiscoveryResources.right_projection : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t a : Fin N), (M8.DiscoveryResources.rightRun c e t a).selected.map Prod.snd = M8.Discovery.atRight c e t a := by
  intro N inst c e t a
  have h := congrArg Prod.fst (M8.WeightedSearch.find_projection N (M8.Discovery.Choice N)
    (fun b : Fin N =>
      (if M8.Discovery.test c ⟨e, t, a, b⟩ then some ⟨e, t, a, b⟩ else none,
        M8.DiscoveryResources.leafCharge c ⟨e, t, a, b⟩)))
  simpa only [M8.DiscoveryResources.rightRun, M8.Discovery.atRight] using
    congrArg (Option.map Prod.snd) h

theorem M8.DiscoveryResources.left_projection : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t : Fin N), (M8.DiscoveryResources.leftRun c e t).selected.map Prod.snd = M8.Discovery.atLeft c e t := by
  intro N inst c e t
  have h := congrArg Prod.fst (M8.WeightedSearch.find_projection N (M8.Discovery.Choice N)
    (fun a : Fin N =>
      ((M8.DiscoveryResources.rightRun c e t a).selected.map Prod.snd,
        M8.DiscoveryResources.charged N (M8.DiscoveryResources.rightRun c e t a))))
  simpa only [M8.DiscoveryResources.leftRun, M8.Discovery.atLeft,
    M8.DiscoveryResources.right_projection] using congrArg (Option.map Prod.snd) h

theorem M8.DiscoveryResources.unit_projection : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ e : Bool, (M8.DiscoveryResources.unitRun c e).selected.map Prod.snd = M8.Discovery.atUnit c e := by
  intro N inst c e
  have h := congrArg Prod.fst (M8.WeightedSearch.find_projection N (M8.Discovery.Choice N)
    (fun t : Fin N =>
      ((M8.DiscoveryResources.leftRun c e t).selected.map Prod.snd,
        M8.DiscoveryResources.charged N (M8.DiscoveryResources.leftRun c e t))))
  simpa only [M8.DiscoveryResources.unitRun, M8.Discovery.atUnit,
    M8.DiscoveryResources.left_projection] using congrArg (Option.map Prod.snd) h
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.DiscoveryResources.run c).selected.map Prod.snd = M8.Discovery.discover c
