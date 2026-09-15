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
#print axioms M7.OverfullBoundary.class_impossible
#print axioms M7.OverfullBoundary.empty_root
#print axioms M7.OverfullBoundary.empty_generate
