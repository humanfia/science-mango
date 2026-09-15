import M5PrefixPartition


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ)
