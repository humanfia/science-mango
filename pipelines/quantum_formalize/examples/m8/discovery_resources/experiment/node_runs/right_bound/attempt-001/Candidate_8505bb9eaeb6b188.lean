import FrozenTarget_8505bb9eaeb6b188
theorem M8.DiscoveryResources.right_bound : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (e : Bool) (t a : Fin N), M8.DiscoveryResources.charged N (M8.DiscoveryResources.rightRun c e t a) ≤ 136 * (N + 1)^4
  intro N inst c e t a
  have h := M8.WeightedSearch.total_bound N (M8.Discovery.Choice N)
    (fun b : Fin N =>
      (if M8.Discovery.test c ⟨e,t,a,b⟩ then some ⟨e,t,a,b⟩ else none,
        M8.DiscoveryResources.leafCharge c ⟨e,t,a,b⟩))
    (128 * (N + 1)^3) (M8.DiscoveryResources.control N)
    (fun b => M8.DiscoveryResources.leaf_bound N c ⟨e,t,a,b⟩)
  calc
    M8.DiscoveryResources.charged N (M8.DiscoveryResources.rightRun c e t a)
        ≤ N * (M8.DiscoveryResources.control N + 128 * (N + 1)^3) := by
          simpa only [M8.DiscoveryResources.charged, M8.DiscoveryResources.rightRun,
            Nat.add_comm] using h
    _ ≤ 136 * (N + 1)^4 := by
      unfold M8.DiscoveryResources.control
      nlinarith [Nat.zero_le (N^2), Nat.zero_le (N^3), Nat.zero_le (N^4)]
