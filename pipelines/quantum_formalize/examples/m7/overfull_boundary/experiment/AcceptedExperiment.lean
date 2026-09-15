import M7OverfullBoundary

theorem M7.OverfullBoundary.class_impossible : ∀ (N w : ℕ) [NeZero N], N < w → ∀ c : M7.Action.Recipe N, ¬ M7.PrefixOrbit.ClassValid w c := by
  change ∀ (N w : ℕ) [NeZero N], N < w → ∀ c : M7.Action.Recipe N, ¬ M7.PrefixOrbit.ClassValid w c
  intro N w inst hN c hc
  have hcard : c.1.card = w := by
    unfold M7.PrefixOrbit.ClassValid at hc
    aesop
  have hbound := Finset.card_le_univ c.1
  have hle : c.1.card ≤ N := by
    simpa only [ZMod.card] using hbound
  omega

theorem M7.OverfullBoundary.empty_root : ∀ (N w : ℕ) [NeZero N], 0 < w → M7.CompactGeneration.residual (N := N) w ∅ ∅ [] = 0 := by
  intro N w inst hw
  classical
  simp only [M7.CompactGeneration.residual, Finset.sum_empty, sub_zero]
  unfold M7.PrefixBits.count
  first
  | simpa using (M7.PrefixSector.empty_sector N w _ _ _ _ hw).1
  | simpa using (M7.PrefixSector.empty_sector N w hw _ _ _ _).1
  | simpa using (M7.PrefixSector.empty_sector N w _ _ _ _).1

theorem M7.OverfullBoundary.empty_generate : ∀ (N w : ℕ) [NeZero N], 0 < w → (M7.CompactGeneration.generate (N := N) w ∅).finalBases = ∅ ∧ (M7.CompactGeneration.generate (N := N) w ∅).emitted = [] ∧ (M7.CompactGeneration.generate (N := N) w ∅).finalResidual = 0 ∧ (M7.CompactGeneration.generate (N := N) w ∅).fuelExhausted = false := by
  intro N w inst hw
  classical
  unfold M7.CompactGeneration.generate
  simp [M7.OverfullBoundary.empty_root N w hw, M7.CompactGeneration.run]

theorem M7.OverfullBoundary.overfull_generate : ∀ (N w : ℕ) [NeZero N], ∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → N < w → (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ ∧ (M7.CompactGeneration.generate (N := N) w E).emitted = [] ∧ (M7.CompactGeneration.generate (N := N) w E).finalResidual = 0 ∧ (M7.CompactGeneration.generate (N := N) w E).fuelExhausted = false := by
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
  exact ⟨hb, he, hex.2.1, hex.2.2.1⟩
#print axioms M7.OverfullBoundary.class_impossible
#print axioms M7.OverfullBoundary.empty_root
#print axioms M7.OverfullBoundary.empty_generate
#print axioms M7.OverfullBoundary.overfull_generate
