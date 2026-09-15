import M5Packing


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.packedValue r i % T = (r i).val
