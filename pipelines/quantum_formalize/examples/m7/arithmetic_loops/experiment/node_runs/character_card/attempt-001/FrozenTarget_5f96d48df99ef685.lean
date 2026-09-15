import M7ArithmeticLoops


def QuantumHarnessFrozenTarget : Prop :=
  ∀ D : ℕ, Fintype.card (M5.Character.BinaryVector D) = 2^D
