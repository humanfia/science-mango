import FrozenTarget_b0572aa06e45e4aa
theorem M6.Flatten.flatten_add : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (z w : M6.Physical.Word N), M6.Flatten.flatten N (z + w) = M6.Flatten.flatten N z + M6.Flatten.flatten N w
  intro N z w
  funext i
  by_cases h : i.val < N <;> simp [M6.Flatten.flatten, h]
