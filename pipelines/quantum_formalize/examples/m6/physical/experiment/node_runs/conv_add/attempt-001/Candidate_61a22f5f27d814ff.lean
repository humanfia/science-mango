import FrozenTarget_61a22f5f27d814ff
theorem M6.Physical.conv_add : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a u v
  funext i
  simp only [M6.Physical.conv, Pi.add_apply, mul_add, Finset.sum_add_distrib]
