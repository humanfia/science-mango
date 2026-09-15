import FrozenTarget_80ffeb5a78f9932a
theorem M5.GlobalCriterion.positive_bounded_progression : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0 hA
  cases w with
  | zero => omega
  | succ k =>
    have hT : 0 < M5.signaturePeriod F :=
      (M5.Period.period_law F hF hF0).1
    obtain ⟨a, b, hab⟩ :=
      (M5.ResidueCount.period_A_exact (k + 1) F (by omega) hF hF0).2.2.mp hA
    simp only [Nat.add_sub_cancel] at a b hab
    let r := M5.ResidueTailBridge.anchored hT a
    let s := M5.ResidueTailBridge.anchored hT b
    have hr : M5.BoundedConstruction.anchoredTuple r := by
      exact M5.ResidueTailBridge.anchor_zero _ _ hT a
    have hs : M5.BoundedConstruction.anchoredTuple s := by
      exact M5.ResidueTailBridge.anchor_zero _ _ hT b
    unfold M5.ResidueCount.feasible at hab
    have hg : M5.BoundedConstruction.tupleSupportGcd r s = 1 := by
      simpa [r, s, M5.BoundedConstruction.tupleSupportGcd,
        M5.ResidueCount.residueSupport, M5.Connectivity.supportGcd,
        Finset.gcd_image, Finset.gcd_union,
        M5.ResidueTailBridge.gcd_cons, Nat.gcd_assoc] using hab.1
    have hp : M5.completeSignature
        (M5.SupportPolynomial.ofResidueTuple r)
        (M5.SupportPolynomial.ofResidueTuple s) (M5.signaturePeriod F) = F := by
      simpa [r, s, M5.ResidueTailBridge.polynomial_cons,
        M5.ResidueCount.tailPolynomial] using hab.2
    obtain ⟨S, N, E, hE, hN, hprog⟩ :=
      M5.FeasibleSource.same_support_infinite_progression
        (k + 1) (M5.signaturePeriod F) r s F hw hT hr hs hg hp
    exact ⟨S, M5.Packing.packedSupport s, N, E, hE, hN, hprog⟩
