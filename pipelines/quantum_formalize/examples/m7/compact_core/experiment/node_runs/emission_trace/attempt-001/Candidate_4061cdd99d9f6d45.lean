import FrozenTarget_4061cdd99d9f6d45
theorem M7.CompactGeneration.emission_trace : QuantumHarnessFrozenTarget := by
  by
    intro N inst w E bases
    change M7.DescentTrace.check (M7.CompactGeneration.residual w E bases) []
      (M7.DescentTrace.trace (M7.CompactGeneration.residual w E bases) []
        (M7.PrefixBits.depth N)) = (true, 2 * M7.PrefixBits.depth N)
    exact M7.DescentTrace.check_trace _ _ _
