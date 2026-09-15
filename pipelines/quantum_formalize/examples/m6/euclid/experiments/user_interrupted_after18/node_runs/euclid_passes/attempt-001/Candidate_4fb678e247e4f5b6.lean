import FrozenTarget_4fb678e247e4f5b6
theorem M6.Euclid.euclid_passes : QuantumHarnessFrozenTarget := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.euclid p q).passes = 2 * (M6.Euclid.euclid p q).cancellations + 3 * (M6.Euclid.euclid p q).rounds + 2
  intro p q
  simp [M6.Euclid.euclid, M6.Euclid.euclid_aux_passes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
