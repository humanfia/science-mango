import FrozenTarget_b205aaec7955c266
theorem M5.BinaryRecovery.recover_valid : QuantumHarnessFrozenTarget := by
  change ∀ (c : List Bool → ℤ) (Valid : List Bool → Prop) (m : ℕ), (∀ q : List Bool, q.length < m → c q = c (q ++ [false]) + c (q ++ [true])) → (∀ q : List Bool, q.length = m → 0 < c q → Valid q) → 0 < c [] → (M5.BinaryRecovery.recover c [] m).length = m ∧ Valid (M5.BinaryRecovery.recover c [] m)
  intro c Valid m hs hv hp
  have hlen : (M5.BinaryRecovery.recover c [] m).length = m := by
    simpa only [List.length_nil, Nat.zero_add] using M5.BinaryRecovery.recover_length c [] m
  refine ⟨hlen, hv _ hlen ?_⟩
  apply M5.BinaryRecovery.recover_positive c [] m
  · simpa only [List.length_nil, Nat.zero_add] using hs
  · exact hp
