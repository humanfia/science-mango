import M5Character


def QuantumHarnessFrozenTarget : Prop :=
  ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c
