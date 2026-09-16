import FrozenTarget_bfad04421f611def
theorem M8.DiscoveryResources.work_bound : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.DiscoveryResources.work c ≤ 320 * (N + 1)^6
  intro N inst c
  have h := M8.WeightedSearch.total_bound 2 (M8.Discovery.Choice N)
    (fun e : Fin 2 =>
      let r := M8.DiscoveryResources.unitRun c (decide (e.val = 1))
      (r.selected.map Prod.snd, M8.DiscoveryResources.charged N r))
    (152 * (N + 1)^6) (M8.DiscoveryResources.control N)
    (fun e => M8.DiscoveryResources.unit_bound N c (decide (e.val = 1)))
  calc
    M8.DiscoveryResources.work c
        ≤ 2 * (M8.DiscoveryResources.control N + 152 * (N + 1)^6) := by
          simpa only [M8.DiscoveryResources.work, M8.DiscoveryResources.charged,
            M8.DiscoveryResources.run, Nat.add_comm] using h
    _ ≤ 320 * (N + 1)^6 := by
      unfold M8.DiscoveryResources.control
      nlinarith [Nat.zero_le (N^2), Nat.zero_le (N^3), Nat.zero_le (N^4),
        Nat.zero_le (N^5), Nat.zero_le (N^6)]
