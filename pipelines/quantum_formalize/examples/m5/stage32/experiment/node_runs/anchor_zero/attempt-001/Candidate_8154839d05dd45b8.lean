import FrozenTarget_8154839d05dd45b8
theorem M5.ResidueTailBridge.anchor_zero : QuantumHarnessFrozenTarget := by
  change ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), ∀ i : Fin (k + 1), i.val = 0 → (M5.ResidueTailBridge.anchored hT r i).val = 0
  intro T k hT r i hi
  have hi0 : i = 0 := Fin.ext hi
  subst i
  simp [M5.ResidueTailBridge.anchored, Fin.cons_zero]
