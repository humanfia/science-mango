import FrozenTarget_10113c542db6d943
theorem M6.FixedSpan.recipe_signature : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, 3 ∣ N → M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N) = M6.FixedSpan.recipe
  intro N hN
  simp [M6.Cyclic.signature, EuclideanDomain.gcd_self, EuclideanDomain.gcd_eq_left, M6.FixedSpan.recipe_divides N hN]
