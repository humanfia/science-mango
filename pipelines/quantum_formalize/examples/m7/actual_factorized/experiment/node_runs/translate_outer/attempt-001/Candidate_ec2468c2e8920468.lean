import FrozenTarget_ec2468c2e8920468
theorem M7.ActualFactorized.translate_outer : QuantumHarnessFrozenTarget := by
  intro N inst c g
  change M7.Action.act g c = M7.Action.act (M7.Action.translate g.leftShift g.rightShift) (M7.Action.act { unit := g.unit, exchange := g.exchange, leftShift := 0, rightShift := 0 } c)
  rw [← M7.Action.act_compose]
  congr 1
  cases g
  simp [M7.Action.compose, M7.Action.translate]
