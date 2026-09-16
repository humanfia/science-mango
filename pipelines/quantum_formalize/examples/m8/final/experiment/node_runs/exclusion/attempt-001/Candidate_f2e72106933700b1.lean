import FrozenTarget_f2e72106933700b1
theorem M8.Final.exclusion : QuantumHarnessFrozenTarget := by
  change M8.Final.ExcludedFamilies
  unfold M8.Final.ExcludedFamilies
  exact ⟨M8.Exclusion.span_rejected, M8.Exclusion.weight_rejected, M8.Exclusion.antipodal_span, M8.Exclusion.antipodal_distance, M8.Exclusion.antipodal_rejected, M8.Exclusion.antipodal_complete⟩
