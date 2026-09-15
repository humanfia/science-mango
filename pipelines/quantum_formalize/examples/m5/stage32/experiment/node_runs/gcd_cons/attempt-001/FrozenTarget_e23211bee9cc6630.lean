import M5ResidueTailBridge


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), Finset.univ.gcd (fun i : Fin (k + 1) => (M5.ResidueTailBridge.anchored hT r i).val) = Finset.univ.gcd (fun i : Fin k => (r i).val)
