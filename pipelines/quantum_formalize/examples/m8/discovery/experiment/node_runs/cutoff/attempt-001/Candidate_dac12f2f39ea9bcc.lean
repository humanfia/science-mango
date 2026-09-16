import FrozenTarget_dac12f2f39ea9bcc
theorem M8.Discovery.cutoff : QuantumHarnessFrozenTarget := by
  intro N _ c k h
  exact (M8.Discovery.sound N c k h).2.2
