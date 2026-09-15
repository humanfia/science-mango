import FrozenTarget_ead2ecec737110d6
theorem M7.CompactGeneration.emission_stabilizer : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst w E bases
  change 0 < M7.ActualFactorized.stabilizerNumerator (M7.CompactGeneration.emission w E bases).representative ∧ M7.ActualFactorized.stabilizerNumerator (M7.CompactGeneration.emission w E bases).representative = M7.ActualOrbit.stabilizerCount (M7.CompactGeneration.emission w E bases).representative
  constructor
  · rw [M7.ActualFactorized.stabilizer_numerator N]
    exact?
  · exact M7.ActualFactorized.stabilizer_numerator N _
