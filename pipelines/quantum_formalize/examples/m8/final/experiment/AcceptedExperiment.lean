import M8Final

theorem M8.Final.algorithm : M8.Final.Algorithm := by
  change M8.Final.Algorithm
  unfold M8.Final.Algorithm
  exact ⟨M8.Solver.output_gcd, M8.Solver.noLogical_exact, M8.Solver.unrecognized_exact, M8.Solver.recognized_exact, M8.Solver.recognized_correct⟩

theorem M8.Final.cost_projection : M8.Final.CostProjection := by
  change M8.Final.CostProjection
  unfold M8.Final.CostProjection
  exact M8.WholeResources.projection

theorem M8.Final.coverage : M8.Final.AdmittedFamilies := by
  change M8.Final.AdmittedFamilies
  unfold M8.Final.AdmittedFamilies
  exact ⟨M8.Coverage.p3_physical, M8.Coverage.p3_recognized, M8.Coverage.p4_physical, M8.Coverage.p4_recognized, M8.Coverage.p4_full_multiplicity, M8.Coverage.mixed_recognized⟩

theorem M8.Final.exclusion : M8.Final.ExcludedFamilies := by
  change M8.Final.ExcludedFamilies
  unfold M8.Final.ExcludedFamilies
  exact ⟨M8.Exclusion.span_rejected, M8.Exclusion.weight_rejected, M8.Exclusion.antipodal_span, M8.Exclusion.antipodal_distance, M8.Exclusion.antipodal_rejected, M8.Exclusion.antipodal_complete⟩

theorem M8.Final.physical_parameters : M8.Final.PhysicalParameters := by
  change M8.Final.PhysicalParameters
  unfold M8.Final.PhysicalParameters
  exact ⟨M8.RawParameters.raw_noLogical, M8.RawParameters.encoded_dimension⟩

theorem M8.Final.resources : M8.Final.Resources := by
  change M8.Final.Resources
  unfold M8.Final.Resources
  exact ⟨M8.SequentialResources.actual_prefix_charge, M8.SequentialResources.sequential_bound⟩

theorem M8.Final.storage : M8.Final.Storage := by
  change M8.Final.Storage
  unfold M8.Final.Storage
  exact ⟨M8.SequentialStore.allocation_access, M8.SequentialStore.store_space⟩

theorem M8.Final.original_m8 : M8.Final.OriginalM8 := by
  change M8.Final.OriginalM8
  unfold M8.Final.OriginalM8
  exact ⟨M8.Final.algorithm, M8.Final.physical_parameters, M8.Final.resources, M8.Final.storage, M8.Final.cost_projection, M8.Final.coverage, M8.Final.exclusion⟩
#print axioms M8.Final.algorithm
#print axioms M8.Final.cost_projection
#print axioms M8.Final.coverage
#print axioms M8.Final.exclusion
#print axioms M8.Final.physical_parameters
#print axioms M8.Final.resources
#print axioms M8.Final.storage
#print axioms M8.Final.original_m8
