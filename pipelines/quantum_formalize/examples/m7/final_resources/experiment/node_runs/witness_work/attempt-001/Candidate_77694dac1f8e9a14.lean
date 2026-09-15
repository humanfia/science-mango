import FrozenTarget_77694dac1f8e9a14
theorem M7.FinalResources.witness_work : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E hw hwN hE d k v hsolve
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hp := M7.GeneratedLabels.pointwise N w E hw hwN hE i
  have hs := hsolve i
  simp only [M6.Final.PointwiseCorrect, M6.Final.ExecutionCorrect,
    M6.Final.StorageCorrect] at hp
  aesop
