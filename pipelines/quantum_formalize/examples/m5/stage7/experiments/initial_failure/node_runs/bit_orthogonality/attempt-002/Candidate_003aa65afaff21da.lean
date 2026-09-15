import FrozenTarget_003aa65afaff21da
theorem M5.Character.bit_orthogonality : QuantumHarnessFrozenTarget := by
  change ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0
  intro b
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  fin_cases b <;> norm_num [M5.Character.bitSign, huniv]
