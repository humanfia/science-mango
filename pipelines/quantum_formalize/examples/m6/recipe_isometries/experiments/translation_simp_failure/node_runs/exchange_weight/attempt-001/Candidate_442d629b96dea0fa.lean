import FrozenTarget_442d629b96dea0fa
theorem M6.RecipeIsometries.exchange_weight : QuantumHarnessFrozenTarget := by
  intro N inst z
  change M6.Physical.weight N z.2 + M6.Physical.weight N z.1 = M6.Physical.weight N z.1 + M6.Physical.weight N z.2
  exact Nat.add_comm _ _
