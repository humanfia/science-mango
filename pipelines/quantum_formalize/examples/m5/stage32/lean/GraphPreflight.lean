import M5ResidueTailBridge

noncomputable def preflight_anchor_zero : Prop :=
  ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), ∀ i : Fin (k + 1), i.val = 0 → (M5.ResidueTailBridge.anchored hT r i).val = 0

noncomputable def preflight_polynomial_cons : Prop :=
  ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), M5.SupportPolynomial.ofResidueTuple (M5.ResidueTailBridge.anchored hT r) = 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (r i).val

noncomputable def preflight_gcd_cons : Prop :=
  ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), Finset.univ.gcd (fun i : Fin (k + 1) => (M5.ResidueTailBridge.anchored hT r i).val) = Finset.univ.gcd (fun i : Fin k => (r i).val)
