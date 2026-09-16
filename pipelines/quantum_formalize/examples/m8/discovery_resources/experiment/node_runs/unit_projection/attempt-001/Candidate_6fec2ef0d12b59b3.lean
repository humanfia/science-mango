import FrozenTarget_6fec2ef0d12b59b3
theorem M8.DiscoveryResources.unit_projection : QuantumHarnessFrozenTarget := by
  intro N inst c e
  have h := congrArg Prod.fst (M8.WeightedSearch.find_projection N (M8.Discovery.Choice N)
    (fun t : Fin N =>
      ((M8.DiscoveryResources.leftRun c e t).selected.map Prod.snd,
        M8.DiscoveryResources.charged N (M8.DiscoveryResources.leftRun c e t))))
  simpa only [M8.DiscoveryResources.unitRun, M8.Discovery.atUnit,
    M8.DiscoveryResources.left_projection] using congrArg (Option.map Prod.snd) h
