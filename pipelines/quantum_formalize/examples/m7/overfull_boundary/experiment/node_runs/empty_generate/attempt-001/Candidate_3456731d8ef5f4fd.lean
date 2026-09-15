import FrozenTarget_3456731d8ef5f4fd
theorem M7.OverfullBoundary.empty_generate : QuantumHarnessFrozenTarget := by
  intro N w inst hw
  classical
  unfold M7.CompactGeneration.generate
  simp [M7.OverfullBoundary.empty_root N w hw, M7.CompactGeneration.run]
