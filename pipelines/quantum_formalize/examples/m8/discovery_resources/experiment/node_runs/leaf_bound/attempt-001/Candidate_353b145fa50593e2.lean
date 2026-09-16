import FrozenTarget_353b145fa50593e2
theorem M8.DiscoveryResources.leaf_bound : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.DiscoveryResources.leafCharge c k ≤ 128 * (N + 1)^3
  intro N inst c k
  obtain ⟨hlm, hls⟩ := M8.DiscoveryResources.fold_charges N (M8.Anchor.left c k.exchange)
  obtain ⟨hrm, hrs⟩ := M8.DiscoveryResources.fold_charges N (M8.Anchor.right c k.exchange)
  have htotal : 64 * (N + 1)^2 + (4 * N * (N + 1) + (4 * N * (N + 1) + (16 * N * (N + 1)^2 + 16 * N * (N + 1)^2))) ≤ 128 * (N + 1)^3 := by
    nlinarith [Nat.zero_le (N^3), Nat.zero_le (N^2)]
  unfold M8.DiscoveryResources.leafCharge
  repeat split <;> omega
