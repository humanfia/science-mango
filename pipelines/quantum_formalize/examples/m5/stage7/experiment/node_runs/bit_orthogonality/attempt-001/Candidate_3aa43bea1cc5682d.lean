import FrozenTarget_3aa43bea1cc5682d
theorem M5.Character.bit_orthogonality : QuantumHarnessFrozenTarget := by
  change ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0
  decide
