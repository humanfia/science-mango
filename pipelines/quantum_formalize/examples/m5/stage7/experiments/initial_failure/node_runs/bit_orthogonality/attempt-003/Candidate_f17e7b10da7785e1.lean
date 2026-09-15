import FrozenTarget_f17e7b10da7785e1
theorem M5.Character.bit_orthogonality : QuantumHarnessFrozenTarget := by
  change ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  intro b
  fin_cases b <;> norm_num [huniv, M5.Character.bitSign]
