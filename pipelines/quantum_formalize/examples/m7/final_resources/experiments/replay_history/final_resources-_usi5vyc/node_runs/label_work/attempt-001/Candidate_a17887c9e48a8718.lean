import FrozenTarget_a17887c9e48a8718
theorem M7.FinalResources.label_work : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE
  classical
  have hp := M7.GeneratedLabels.pointwise N w E hw hwN hE
  constructor
  · unfold M7.FinalResources.distanceWork
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := hp i
    simp only [M6.Final.PointwiseCorrect, M6.Final.ExecutionCorrect,
      M6.Final.StorageCorrect] at h
    aesop
  · intro i
    have h := hp i
    simp only [M6.Final.PointwiseCorrect, M6.Final.ExecutionCorrect,
      M6.Final.StorageCorrect] at h
    aesop
