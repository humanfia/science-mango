import FrozenTarget_c62654e71dc089a9
theorem M7.OverfullBoundary.overfull_generate : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) [NeZero N], ∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → N < w → _
  intro N w inst E hE hw
  have hex := M7.CompactCorrectness.generate_exact N w E hE
  have hg : M7.RecoveryInstance.GoodBases w (M7.CompactGeneration.generate (N := N) w E).finalBases := by
    aesop
  have hb : (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ := by
    apply Finset.ext
    intro c
    simp only [Finset.notMem_empty, iff_false]
    intro hc
    apply M7.OverfullBoundary.class_impossible N w hw c
    unfold M7.RecoveryInstance.GoodBases at hg
    aesop
  have hcard := M7.CompactCorrectness.generate_card N w E hE
  have he : (M7.CompactGeneration.generate (N := N) w E).emitted = [] := by
    apply List.length_eq_zero.mp
    simpa [hb] using hcard
  exact ⟨hb, he, by aesop⟩
