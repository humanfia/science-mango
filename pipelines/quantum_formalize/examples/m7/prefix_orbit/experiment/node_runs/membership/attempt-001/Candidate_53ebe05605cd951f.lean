import FrozenTarget_53ebe05605cd951f
theorem M7.PrefixOrbit.membership : QuantumHarnessFrozenTarget := by
  by
    intro N inst w E A B WA WB hbase y
    classical
    rw [M7.ResiduePrefix.completed_membership N w E A B WA WB hbase y]
    have hw : M7.PrefixCompleted.Within A B WA WB (M7.ResiduePrefix.encodePair y) ↔
        M7.PrefixOrbit.Within A WA y.1 ∧ M7.PrefixOrbit.Within B WB y.2 := by
      unfold M7.PrefixCompleted.Within M7.ResiduePrefix.encodePair M7.PrefixOrbit.Within
      tauto
    have hv (hA : M7.PrefixOrbit.Within A WA y.1)
        (hB : M7.PrefixOrbit.Within B WB y.2) :
        M7.PrefixCompleted.Valid N w E (M7.ResiduePrefix.encodePair y) ↔
          M7.PrefixOrbit.ClassValid w y ∧ M7.RecipeSignature.signature y ∈ E := by
      obtain ⟨ha, hb⟩ := M7.PrefixOrbit.prefix_anchors N A B WA WB y hbase hA hB
      have hc : M7.Connectivity.connected y ↔
          M5.Connectivity.supportGcd N (M7.ResiduePrefix.encode y.1)
            (M7.ResiduePrefix.encode y.2) = 1 := by
        rw [← M7.PrefixOrbit.gcd_bridge N y]
        exact M7.Connectivity.anchored_gcd N y.1 y.2 ha hb
      simp only [M7.PrefixCompleted.Valid, M7.ResiduePrefix.encodePair,
        M7.ResiduePrefix.encode_card, M7.ResiduePrefix.signature_bridge,
        M7.PrefixOrbit.ClassValid, M7.RecipeSignature.signature]
      tauto
    constructor
    · intro h
      obtain ⟨hA, hB⟩ := hw.mp h.1
      obtain ⟨hc, hs⟩ := (hv hA hB).mp h.2
      exact ⟨hc, hs, hA, hB⟩
    · rintro ⟨hc, hs, hA, hB⟩
      exact ⟨hw.mpr ⟨hA, hB⟩, (hv hA hB).mpr ⟨hc, hs⟩⟩
