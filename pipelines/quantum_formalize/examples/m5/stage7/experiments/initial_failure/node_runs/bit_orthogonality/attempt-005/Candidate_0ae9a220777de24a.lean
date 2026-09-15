import FrozenTarget_0ae9a220777de24a
theorem M5.Character.bit_orthogonality : QuantumHarnessFrozenTarget := by
  change ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    ext a
    fin_cases a <;> simp
  have hval : (1 : ZMod 2).val = 1 := rfl
  intro b
  fin_cases b <;> norm_num [huniv, M5.Character.bitSign, hval]
