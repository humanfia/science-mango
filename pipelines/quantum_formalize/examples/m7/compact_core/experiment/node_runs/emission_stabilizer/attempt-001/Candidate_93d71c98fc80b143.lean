import FrozenTarget_93d71c98fc80b143
theorem M7.CompactGeneration.emission_stabilizer : QuantumHarnessFrozenTarget := by
  by
    intro N inst w E bases
    change 0 < M7.ActualFactorized.stabilizerNumerator (M7.CompactGeneration.emission w E bases).representative ∧ M7.ActualFactorized.stabilizerNumerator (M7.CompactGeneration.emission w E bases).representative = M7.ActualOrbit.stabilizerCount (M7.CompactGeneration.emission w E bases).representative
    rw [M7.ActualFactorized.stabilizer_numerator N]
    constructor
    · exact?
    · rfl
