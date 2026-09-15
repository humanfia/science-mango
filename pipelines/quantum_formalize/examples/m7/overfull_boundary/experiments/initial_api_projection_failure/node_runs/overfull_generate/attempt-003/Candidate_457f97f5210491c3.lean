import FrozenTarget_457f97f5210491c3
theorem M7.OverfullBoundary.overfull_generate : QuantumHarnessFrozenTarget := by
    change ∀ (N w : ℕ) [NeZero N], ∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → N < w → _
    intro N w inst E hE hN
    classical
    have hex := M7.CompactCorrectness.generate_exact N w E hE
    have hb : (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro c hc
      have hg := hex.1
      have hv : M7.PrefixOrbit.ClassValid w c := by
        unfold M7.RecoveryInstance.GoodBases at hg
        aesop
      exact M7.OverfullBoundary.class_impossible N w hN c hv
    have hcard := M7.CompactCorrectness.generate_card N w E hE
    simp only [hb, Finset.card_empty] at hcard
    have he : (M7.CompactGeneration.generate (N := N) w E).emitted = [] := by
      apply List.length_eq_zero_iff.mp
      omega
    exact ⟨hb, he, hex.2.1, hex.2.2.1⟩
