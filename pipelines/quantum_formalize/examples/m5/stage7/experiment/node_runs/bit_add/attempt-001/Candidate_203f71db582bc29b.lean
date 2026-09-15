import FrozenTarget_203f71db582bc29b
theorem M5.Character.bit_add : QuantumHarnessFrozenTarget := by
  change ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c
  decide
