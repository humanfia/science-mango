import FrozenTarget_76573c7fa6d31306
theorem M5.Character.bit_orthogonality : QuantumHarnessFrozenTarget := by
  change ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0
  intro b
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv]
  simp only [Finset.sum_insert (by decide : (0 : ZMod 2) ∉ ({1} : Finset (ZMod 2))), Finset.sum_singleton]
  fin_cases b
  · change M5.Character.bitSign 0 0 + M5.Character.bitSign 1 0 = 2
    norm_num [M5.Character.bitSign]
  · change M5.Character.bitSign 0 1 + M5.Character.bitSign 1 1 = 0
    norm_num [M5.Character.bitSign]
