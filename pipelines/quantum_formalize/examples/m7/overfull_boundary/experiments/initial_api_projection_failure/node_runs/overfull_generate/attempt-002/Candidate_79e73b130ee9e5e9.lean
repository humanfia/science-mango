import FrozenTarget_79e73b130ee9e5e9
theorem M7.OverfullBoundary.overfull_generate : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) [NeZero N], ∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → N < w → (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ ∧ (M7.CompactGeneration.generate (N := N) w E).emitted = [] ∧ (M7.CompactGeneration.generate (N := N) w E).finalResidual = 0 ∧ (M7.CompactGeneration.generate (N := N) w E).fuelExhausted = false
  intro N w inst E hE hN
  classical
  have hex := M7.CompactCorrectness.generate_exact N w E hE
  have hgood : M7.RecoveryInstance.GoodBases w (M7.CompactGeneration.generate (N := N) w E).finalBases := hex.1
  have hb : (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ := by
    ext c
    constructor
    · intro hc
      have hv : M7.PrefixOrbit.ClassValid w c := by
        unfold M7.RecoveryInstance.GoodBases at hgood
        aesop
      exact False.elim (M7.OverfullBoundary.class_impossible N w hN c hv)
    · intro hc
      simpa using hc
  have hcard := M7.CompactCorrectness.generate_card N w E hE
  have he : (M7.CompactGeneration.generate (N := N) w E).emitted = [] := by
    cases hl : (M7.CompactGeneration.generate (N := N) w E).emitted with
    | nil => rfl
    | cons a l => simp [hb, hl] at hcard
  exact ⟨hb, he, hex.2⟩
