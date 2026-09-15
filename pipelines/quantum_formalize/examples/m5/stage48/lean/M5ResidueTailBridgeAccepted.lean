import M5ResidueTailBridge

theorem M5.ResidueTailBridge.anchor_zero : ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), ∀ i : Fin (k + 1), i.val = 0 → (M5.ResidueTailBridge.anchored hT r i).val = 0 := by
  change ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), ∀ i : Fin (k + 1), i.val = 0 → (M5.ResidueTailBridge.anchored hT r i).val = 0
  intro T k hT r i hi
  have hi0 : i = 0 := Fin.ext hi
  subst i
  simp [M5.ResidueTailBridge.anchored, Fin.cons_zero]

theorem M5.ResidueTailBridge.gcd_cons : ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), Finset.univ.gcd (fun i : Fin (k + 1) => (M5.ResidueTailBridge.anchored hT r i).val) = Finset.univ.gcd (fun i : Fin k => (r i).val) := by
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

theorem M5.ResidueTailBridge.polynomial_cons : ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), M5.SupportPolynomial.ofResidueTuple (M5.ResidueTailBridge.anchored hT r) = 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (r i).val := by
  intro T k hT r
  simp [M5.SupportPolynomial.ofResidueTuple, M5.ResidueTailBridge.anchored, Fin.sum_univ_succ]
#print axioms M5.ResidueTailBridge.anchor_zero
#print axioms M5.ResidueTailBridge.gcd_cons
#print axioms M5.ResidueTailBridge.polynomial_cons
