import M7OverfullBoundary

theorem M7.OverfullBoundary.empty_root : ∀ (N w : ℕ) [NeZero N], 0 < w → M7.CompactGeneration.residual (N := N) w ∅ ∅ [] = 0 := by
  intro N w inst hw
  classical
  simp only [M7.CompactGeneration.residual, Finset.sum_empty, sub_zero]
  unfold M7.PrefixBits.count
  first
  | simpa using (M7.PrefixSector.empty_sector N w _ _ _ _ hw).1
  | simpa using (M7.PrefixSector.empty_sector N w hw _ _ _ _).1
  | simpa using (M7.PrefixSector.empty_sector N w _ _ _ _).1
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N], 0 < w → (M7.CompactGeneration.generate (N := N) w ∅).finalBases = ∅ ∧ (M7.CompactGeneration.generate (N := N) w ∅).emitted = [] ∧ (M7.CompactGeneration.generate (N := N) w ∅).finalResidual = 0 ∧ (M7.CompactGeneration.generate (N := N) w ∅).fuelExhausted = false
