import FrozenTarget_d912eb29ddfcb584
theorem M7.Final.resources : QuantumHarnessFrozenTarget := by
  change M7.Final.Resources
  unfold M7.Final.Resources
  exact ⟨M7.FinalResources.generation,
    M7.FinalResources.storage,
    M7.FinalResources.label_work,
    M7.FinalResources.witness_work,
    M7.FinalResources.word_width,
    M7.FinalResources.comparison,
    M7.ScalarWork.prefix_bound,
    M7.ScalarWork.sector_bound,
    M7.ScalarWork.mask_positions,
    M7.CompactStorage.emission_valid,
    M7.CompactStorage.encode_core,
    M7.CompactStorage.unit_table_recovery,
    M7.CompactStorage.storage_bounds,
    M7.GenerationCalls.generate_count,
    M7.StreamingCost.stream_projection_bound,
    M7.StreamingCost.scan_bound,
    M7.StreamingCost.record_cardinality,
    M7.ObjectiveComparison.compare_exact,
    M7.ObjectiveComparison.compare_bound⟩
