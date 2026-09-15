import M5PhysicalBridge


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T d : ℕ) (r : Fin w → Fin T), d ∣ T → ((∀ a ∈ M5.Packing.packedSupport r, d ∣ a) ↔ ∀ i, d ∣ (r i).val)
