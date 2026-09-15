import FrozenTarget_61615696b7704465
theorem M6.Transfer.output_convolution : QuantumHarnessFrozenTarget := by
  intro R N c h i
  simp [M6.Transfer.output, M6.Transfer.cyclicOutput, M6.Transfer.memoryAt, Fin.sum_univ_succ]
