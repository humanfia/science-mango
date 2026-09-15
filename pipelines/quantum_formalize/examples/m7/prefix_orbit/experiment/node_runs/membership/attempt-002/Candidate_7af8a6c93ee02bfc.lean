import FrozenTarget_7af8a6c93ee02bfc
theorem M7.PrefixOrbit.membership : QuantumHarnessFrozenTarget := by
  intro N inst w E A B WA WB hbase y
  classical
  have hs : M5.completeSignature
      (M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode y.1))
      (M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode y.2)) N =
      M7.RecipeSignature.signature y :=
    M7.ResiduePrefix.signature_bridge N y.1 y.2
  have hm := M7.ResiduePrefix.completed_membership N w E A B WA WB hbase y
  simp only [M7.PrefixCompleted.Within, M7.PrefixCompleted.Valid,
    M7.ResiduePrefix.encodePair, M7.ResiduePrefix.encode_card, hs,
    ← M7.PrefixOrbit.gcd_bridge N y] at hm
  constructor
  · intro hy
    have hp := hm.mp hy
    have hA : M7.PrefixOrbit.Within A WA y.1 := by
      unfold M7.PrefixOrbit.Within
      tauto
    have hB : M7.PrefixOrbit.Within B WB y.2 := by
      unfold M7.PrefixOrbit.Within
      tauto
    obtain ⟨ha, hb⟩ := M7.PrefixOrbit.prefix_anchors N A B WA WB y hbase hA hB
    have hc := M7.Connectivity.anchored_gcd N y.1 y.2 ha hb
    change M7.Connectivity.connected y ↔ M7.Domain.connectivityGcd y.1 y.2 = 1 at hc
    unfold M7.PrefixOrbit.ClassValid
    tauto
  · intro hy
    obtain ⟨hv, hs', hA, hB⟩ := hy
    obtain ⟨ha, hb⟩ := M7.PrefixOrbit.prefix_anchors N A B WA WB y hbase hA hB
    have hc := M7.Connectivity.anchored_gcd N y.1 y.2 ha hb
    change M7.Connectivity.connected y ↔ M7.Domain.connectivityGcd y.1 y.2 = 1 at hc
    unfold M7.PrefixOrbit.ClassValid at hv
    unfold M7.PrefixOrbit.Within at hA hB
    apply hm.mpr
    tauto
