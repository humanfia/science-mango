import FrozenTarget_0d334f5591b7b9f2
theorem M8.DiscoveryResources.left_projection : QuantumHarnessFrozenTarget := by
  intro N inst c e t
  have h := congrArg Prod.fst (M8.WeightedSearch.find_projection N (M8.Discovery.Choice N)
    (fun a : Fin N =>
      ((M8.DiscoveryResources.rightRun c e t a).selected.map Prod.snd,
        M8.DiscoveryResources.charged N (M8.DiscoveryResources.rightRun c e t a))))
  simpa only [M8.DiscoveryResources.leftRun, M8.Discovery.atLeft,
    M8.DiscoveryResources.right_projection] using congrArg (Option.map Prod.snd) h
