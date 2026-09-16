import FrozenTarget_3c47ed64421e7b60
theorem M8.Exclusion.weight_rejected : QuantumHarnessFrozenTarget := by
  intro N inst w c hvalid hF hover
  have hw : 0 < w := by omega
  apply M8.Exclusion.span_rejected N w c hw hvalid hF
  apply M8.ExclusionGeometry.weight_exclusion N w (M8.Cutoff.limit N) c
  · exact hvalid.1
  · exact hvalid.2.1
  · exact hover
