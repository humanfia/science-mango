import M5ResidueTailBridge


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), ∀ i : Fin (k + 1), i.val = 0 → (M5.ResidueTailBridge.anchored hT r i).val = 0
