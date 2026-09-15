import FrozenTarget_45f014061fae9f24
theorem M7.OverfullBoundary.overfull_generate : QuantumHarnessFrozenTarget := by
  intro N w inst E hE hN
  have hex := M7.CompactCorrectness.generate_exact N w E hE
  have hgood : M7.RecoveryInstance.GoodBases w (M7.CompactGeneration.generate (N := N) w E).finalBases := by
    aesop
  have hb : (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    apply M7.OverfullBoundary.class_impossible N w hN c
    unfold M7.RecoveryInstance.GoodBases at hgood
    aesop
  have hcard := M7.CompactCorrectness.generate_card N w E hE
  have hlen : (M7.CompactGeneration.generate (N := N) w E).emitted.length = 0 := by
    simp only [hb, Finset.card_empty] at hcard
    omega
  have hempty : (M7.CompactGeneration.generate (N := N) w E).emitted = [] := List.length_eq_zero.mp hlen
  exact ⟨hb, hempty, by aesop⟩
