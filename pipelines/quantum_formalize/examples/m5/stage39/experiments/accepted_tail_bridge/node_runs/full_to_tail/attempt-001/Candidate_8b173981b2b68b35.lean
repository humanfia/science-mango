import FrozenTarget_8b173981b2b68b35
theorem M5.GlobalCriterion.full_to_tail : QuantumHarnessFrozenTarget := by
  intro w T F r s hw hT hr hs hg hp
  cases w with
  | zero => omega
  | succ k =>
    have hr0 : r 0 = ⟨0, hT⟩ := Fin.ext (hr 0 rfl)
    have hs0 : s 0 = ⟨0, hT⟩ := Fin.ext (hs 0 rfl)
    have er : M5.ResidueTailBridge.anchored hT (Fin.tail r) = r := by
      simpa [M5.ResidueTailBridge.anchored, hr0] using Fin.cons_self_tail r
    have es : M5.ResidueTailBridge.anchored hT (Fin.tail s) = s := by
      simpa [M5.ResidueTailBridge.anchored, hs0] using Fin.cons_self_tail s
    unfold M5.BoundedConstruction.tupleSupportGcd at hg
    rw [← er, ← es] at hg hp
    simp only [M5.ResidueTailBridge.gcd_cons] at hg
    simp only [M5.ResidueTailBridge.polynomial_cons] at hp
    refine ⟨Fin.tail r, Fin.tail s, ?_⟩
    clear er es hr0 hs0 hr hs
    simp_all [M5.ResidueCount.feasible, M5.ResidueCount.tailPolynomial,
      M5.ResidueCount.residueSupport, M5.Connectivity.supportGcd,
      Finset.gcd_image, Function.comp_def]
