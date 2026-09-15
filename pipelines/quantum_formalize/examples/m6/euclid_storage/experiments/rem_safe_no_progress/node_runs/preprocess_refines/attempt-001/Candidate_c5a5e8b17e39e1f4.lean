import FrozenTarget_c5a5e8b17e39e1f4
theorem M6.EuclidStorage.preprocess_refines : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro a b M
  have hfirst := M6.EuclidStorage.gcd_start_refines a b M 0 0 0
  have hs := hfirst.1
  have hv := congrArg M6.Euclid.Run.value hfirst.2.2
  have hc := congrArg M6.Euclid.Run.cancellations hfirst.2.2
  have he := congrArg M6.Euclid.Run.rounds hfirst.2.2
  have ht := congrArg M6.Euclid.Run.passes hfirst.2.2
  simp only [M6.EuclidStorage.toRun, M6.EuclidStorage.offset,
    Nat.zero_add, Nat.add_zero] at hv hc he ht
  have hsecond := fun p q saved c e t =>
    (M6.EuclidStorage.gcd_start_refines p q saved c e t).2.2
  dsimp only [M6.EuclidStorage.preprocess]
  rw [hsecond]
  simp [M6.Euclid.preprocess, M6.EuclidStorage.offset,
    hs, hv, hc, he, ht, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
