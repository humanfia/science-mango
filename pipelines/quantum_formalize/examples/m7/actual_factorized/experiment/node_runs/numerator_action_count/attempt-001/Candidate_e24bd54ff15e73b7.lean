import FrozenTarget_e24bd54ff15e73b7
theorem M7.ActualFactorized.numerator_action_count : QuantumHarnessFrozenTarget := by
  intro N inst c E L R hE
  classical
  rw [M7.ActualFactorized.numerator_record_count N]
  unfold M7.ActualFactorized.recordCount M7.ActualOrbit.actionCount
  apply congrArg Finset.card
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [M7.ActualFactorized.sector_compatibility N c E hE g] <;>
    simp [M7.ActualFactorized.leftImage, M7.ActualFactorized.rightImage,
      M7.ActualFactorized.toRecord, M7.Action.act]
