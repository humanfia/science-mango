import M5Character


def QuantumHarnessFrozenTarget : Prop :=
  ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0
