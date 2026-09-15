import FrozenTarget_125ed1a13cee7a63
theorem M7.OverfullBoundary.empty_root : QuantumHarnessFrozenTarget := by
  intro N w inst hw
  classical
  simp only [M7.CompactGeneration.residual, Finset.sum_empty, sub_zero]
  unfold M7.PrefixBits.count
  first
  | simpa using (M7.PrefixSector.empty_sector N w _ _ _ _ hw).1
  | simpa using (M7.PrefixSector.empty_sector N w hw _ _ _ _).1
  | simpa using (M7.PrefixSector.empty_sector N w _ _ _ _).1
