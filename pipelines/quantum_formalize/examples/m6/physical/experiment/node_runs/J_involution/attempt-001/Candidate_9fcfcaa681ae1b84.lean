import FrozenTarget_9fcfcaa681ae1b84
theorem M6.Physical.J_involution : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (z : M6.Physical.Word N), M6.Physical.J N (M6.Physical.J N z) = z
  intro N z
  rcases z with ⟨a, b⟩
  simp [M6.Physical.J, M6.Physical.rev_involution]
