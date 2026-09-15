import FrozenTarget_a29bc95e640f313b
theorem M5.GlobalCriterion.positive_bounded_progression : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro w F hw hF hF0 hA
  cases w with
  | zero => omega
  | succ k =>
    have hT := (M5.Period.period_law F hF hF0).1
    have htails := (M5.ResidueCount.period_A_exact (k + 1) F (by omega) hF hF0).2.2.mp hA
    change ∃ a b : Fin k → Fin (M5.signaturePeriod F), M5.ResidueCount.feasible F a b at htails
    obtain ⟨a, b, hab⟩ := htails
    let r := M5.ResidueTailBridge.anchored hT a
    let s := M5.ResidueTailBridge.anchored hT b
    have hr : M5.BoundedConstruction.anchoredTuple r := by
      exact M5.ResidueTailBridge.anchor_zero (M5.signaturePeriod F) k hT a
    have hs : M5.BoundedConstruction.anchoredTuple s := by
      exact M5.ResidueTailBridge.anchor_zero (M5.signaturePeriod F) k hT b
    have hg : M5.BoundedConstruction.tupleSupportGcd r s = 1 := by
      simpa [M5.BoundedConstruction.tupleSupportGcd, r, s,
        M5.ResidueCount.residueSupport, Finset.gcd_union, Finset.gcd_image,
        Function.comp_def, M5.ResidueTailBridge.gcd_cons] using hab.1
    have hp : M5.completeSignature (M5.SupportPolynomial.ofResidueTuple r)
        (M5.SupportPolynomial.ofResidueTuple s) (M5.signaturePeriod F) = F := by
      simpa [r, s, M5.ResidueTailBridge.polynomial_cons,
        M5.ResidueCount.tailPolynomial] using hab.2
    obtain ⟨S, N, E, hE, hN, hprogress⟩ :=
      M5.FeasibleSource.same_support_infinite_progression (k + 1)
        (M5.signaturePeriod F) r s F hw hT hr hs hg hp
    exact ⟨S, M5.Packing.packedSupport s, N, E, hE, hN, hprogress⟩
