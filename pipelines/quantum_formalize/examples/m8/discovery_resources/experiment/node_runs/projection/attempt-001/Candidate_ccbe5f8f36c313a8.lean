import FrozenTarget_ccbe5f8f36c313a8
theorem M8.DiscoveryResources.projection : QuantumHarnessFrozenTarget := by
  intro N inst c
  have h := congrArg Prod.fst (M8.WeightedSearch.find_projection 2 (M8.Discovery.Choice N)
    (fun e : Fin 2 =>
      ((M8.DiscoveryResources.unitRun c (decide (e.val = 1))).selected.map Prod.snd,
        M8.DiscoveryResources.charged N (M8.DiscoveryResources.unitRun c (decide (e.val = 1))))))
  simpa only [M8.DiscoveryResources.run, M8.Discovery.discover,
    M8.DiscoveryResources.unit_projection] using congrArg (Option.map Prod.snd) h
