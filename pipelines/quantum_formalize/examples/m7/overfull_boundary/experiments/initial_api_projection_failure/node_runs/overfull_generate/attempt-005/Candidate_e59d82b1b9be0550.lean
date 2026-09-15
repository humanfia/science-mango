import FrozenTarget_e59d82b1b9be0550
theorem M7.OverfullBoundary.overfull_generate : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) [NeZero N], ∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → N < w → _
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
  rw [hb] at hcard
  have hem : (M7.CompactGeneration.generate (N := N) w E).emitted = [] := by
    cases he : (M7.CompactGeneration.generate (N := N) w E).emitted with
    | nil => rfl
    | cons a l => simp [he] at hcard
  exact ⟨hb, hem, by aesop⟩
