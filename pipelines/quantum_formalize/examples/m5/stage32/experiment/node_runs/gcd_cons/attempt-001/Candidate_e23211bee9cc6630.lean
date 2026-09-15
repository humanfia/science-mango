import FrozenTarget_e23211bee9cc6630
theorem M5.ResidueTailBridge.gcd_cons : QuantumHarnessFrozenTarget := by
  intro T k hT r
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd_iff.mpr
    intro i hi
    simpa [M5.ResidueTailBridge.anchored] using
      (Finset.gcd_dvd (s := Finset.univ)
        (f := fun j : Fin (k + 1) => (M5.ResidueTailBridge.anchored hT r j).val)
        (Finset.mem_univ i.succ))
  · apply Finset.dvd_gcd_iff.mpr
    intro i hi
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [M5.ResidueTailBridge.anchored]
    · simpa [M5.ResidueTailBridge.anchored] using
        (Finset.gcd_dvd (s := Finset.univ)
          (f := fun j : Fin k => (r j).val)
          (Finset.mem_univ j))
