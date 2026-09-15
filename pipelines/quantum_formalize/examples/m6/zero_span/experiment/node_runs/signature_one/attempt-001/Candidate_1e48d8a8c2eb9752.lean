import FrozenTarget_1e48d8a8c2eb9752
theorem M6.ZeroSpan.signature_one : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, M6.Cyclic.signature 1 1 (M6.Cyclic.modulus N) = 1
  intro N
  simp [M6.Cyclic.signature]
