import FrozenTarget_49c49bad3f9a91e8
theorem M6.EuclidStorage.gcd_start_refines : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro p q saved c e t
  simpa [M6.EuclidStorage.gcdStart, M6.Euclid.euclid,
    M6.EuclidStorage.offset, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (M6.EuclidStorage.gcd_loop_refines (M6.Euclid.rank q + 1)
      (⟨p, q, 0, saved⟩ : M6.EuclidStorage.Slots) c e (t + 1) rfl)
