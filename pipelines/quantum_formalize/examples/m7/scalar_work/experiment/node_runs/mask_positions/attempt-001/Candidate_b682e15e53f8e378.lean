import FrozenTarget_b682e15e53f8e378
theorem M7.ScalarWork.mask_positions : QuantumHarnessFrozenTarget := by
  intro N inst
  classical
  simp [M7.ScalarWork.maskPositions, M7.ActualFactorized.Outer, Fintype.card_prod, ZMod.card] <;> ring
