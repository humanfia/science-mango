import FrozenTarget_9ec8c87c88def842
theorem M8.DiscoveryResources.left_bound : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t : Fin N), M8.DiscoveryResources.charged N (M8.DiscoveryResources.leftRun c e t) ≤ 144 * (N + 1)^5
  intro N inst c e t
  have h := M8.WeightedSearch.total_bound N (M8.Discovery.Choice N)
    (fun a : Fin N =>
      let r := M8.DiscoveryResources.rightRun c e t a
      (r.selected.map Prod.snd, M8.DiscoveryResources.charged N r))
    (136 * (N + 1)^4) (M8.DiscoveryResources.control N)
    (fun a => M8.DiscoveryResources.right_bound N c e t a)
  calc
    M8.DiscoveryResources.charged N (M8.DiscoveryResources.leftRun c e t)
        ≤ N * (M8.DiscoveryResources.control N + 136 * (N + 1)^4) := by
          simpa only [M8.DiscoveryResources.charged, M8.DiscoveryResources.leftRun,
            Nat.add_comm] using h
    _ ≤ 144 * (N + 1)^5 := by
      unfold M8.DiscoveryResources.control
      nlinarith [Nat.zero_le (N^2), Nat.zero_le (N^3), Nat.zero_le (N^4), Nat.zero_le (N^5)]
