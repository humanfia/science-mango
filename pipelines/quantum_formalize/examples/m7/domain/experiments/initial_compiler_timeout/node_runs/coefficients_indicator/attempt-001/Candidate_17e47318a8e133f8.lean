import FrozenTarget_17e47318a8e133f8
theorem M7.Domain.coefficients_indicator : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst A
  funext i
  change (M7.Supports.polynomial A).coeff i.val = M7.Supports.indicator A i
  exact M7.Supports.indicator_coefficient N A i
