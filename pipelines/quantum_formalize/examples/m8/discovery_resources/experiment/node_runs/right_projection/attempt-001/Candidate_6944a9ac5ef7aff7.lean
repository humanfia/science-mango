import FrozenTarget_6944a9ac5ef7aff7
theorem M8.DiscoveryResources.right_projection : QuantumHarnessFrozenTarget := by
  intro N inst c e t a
  have h := congrArg Prod.fst (M8.WeightedSearch.find_projection N (M8.Discovery.Choice N)
    (fun b : Fin N =>
      (if M8.Discovery.test c ⟨e, t, a, b⟩ then some ⟨e, t, a, b⟩ else none,
        M8.DiscoveryResources.leafCharge c ⟨e, t, a, b⟩)))
  simpa only [M8.DiscoveryResources.rightRun, M8.Discovery.atRight] using
    congrArg (Option.map Prod.snd) h
