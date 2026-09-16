import FrozenTarget_6c86dfb9370d389e
theorem M8.Final.physical_parameters : QuantumHarnessFrozenTarget := by
  change M8.Final.PhysicalParameters
  unfold M8.Final.PhysicalParameters
  exact ⟨M8.RawParameters.raw_noLogical, M8.RawParameters.encoded_dimension⟩
