import FrozenTarget_e5be4d6b1de8f526
theorem M6.RecipeIsometries.exchange_weight : QuantumHarnessFrozenTarget := by
  intro N inst z
  change M6.Physical.weight N z.2 + M6.Physical.weight N z.1 = M6.Physical.weight N z.1 + M6.Physical.weight N z.2
  exact Nat.add_comm _ _
