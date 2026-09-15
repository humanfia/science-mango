import M6Character


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (a b : ZMod 2), M6.Character.sign (a+b) = M6.Character.sign a * M6.Character.sign b
