import Mathlib.Data.Nat.Basic


def QuantumHarnessFrozenTarget : Prop :=
  ∀ a b : Nat, a + b = b + a
