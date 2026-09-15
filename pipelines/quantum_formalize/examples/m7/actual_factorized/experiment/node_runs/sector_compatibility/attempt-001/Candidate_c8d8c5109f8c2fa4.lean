import FrozenTarget_c8d8c5109f8c2fa4
theorem M7.ActualFactorized.sector_compatibility : QuantumHarnessFrozenTarget := by
  intro N inst c E hE g
  rw [M7.ActualFactorized.translate_outer N c g]
  unfold M7.ActualFactorized.TranslationInvariant at hE
  first
  | exact hE _ _ _
  | exact (hE _ _ _).symm
