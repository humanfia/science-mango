import FrozenTarget_94dd66297b8fa28f
theorem M5.Character.bit_add : QuantumHarnessFrozenTarget := by
  change ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [M5.Character.bitSign, ZMod.val]
