import M5Packing


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.occurrenceTag r i < w
