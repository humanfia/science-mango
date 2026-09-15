import M7Final

theorem M7.Final.actionsignature : M7.Final.ActionSignature := by
  change M7.Final.ActionSignature
  unfold M7.Final.ActionSignature
  exact ⟨M7.Action.record_card,
    M7.Action.order_one_records,
    M7.RecipeSignature.signature_properties,
    M7.RecipeSignature.action_signature,
    M7.RecipeSignature.tau_degree,
    M7.RecipeSignature.source_orbit_quotient,
    M7.ActualFactorized.stabilizer_numerator,
    M7.ActualFactorized.positive_denominator,
    M7.ActualFactorized.exact_orbit_quotient,
    M7.PrefixOrbit.residual_card,
    M7.PrefixOrbit.residual_positive⟩

theorem M7.Final.canonical : M7.Final.Canonical := by
  change M7.Final.Canonical
  unfold M7.Final.Canonical
  exact ⟨M7.CanonicalOuter.canonical_minimal,
    M7.CanonicalOuter.realizer_correct,
    M7.CanonicalOuter.realizer_inverse,
    M7.CanonicalOuter.canonical_invariant,
    M7.CanonicalOuter.orbit_complete,
    M7.CanonicalClasses.idempotent⟩

theorem M7.Final.generation : M7.Final.Generation := by
  change M7.Final.Generation
  unfold M7.Final.Generation
  exact ⟨M7.CompactCorrectness.run_records,
    M7.CompactCorrectness.generate_exact,
    M7.CompactCorrectness.generate_card,
    M7.CompactCorrectness.generate_coverage,
    M7.GeneratedFamily.family_range,
    M7.GeneratedFamily.family_good,
    M7.GeneratedFamily.family_anchored,
    M7.GeneratedFamily.family_injective,
    M7.GeneratedFamily.family_separated,
    M7.GeneratedFamily.family_meets,
    M7.GeneratedFamily.family_complete,
    M7.OverfullBoundary.class_impossible,
    M7.OverfullBoundary.overfull_generate,
    M7.OverfullBoundary.empty_root,
    M7.OverfullBoundary.empty_generate,
    M7.QuerySectors.all_sound,
    M7.QuerySectors.all_complete,
    M7.QuerySectors.all_membership,
    M7.QuerySectors.effective_valid,
    M7.QuerySectors.signature_allowed⟩

theorem M7.Final.physicallabels : M7.Final.PhysicalLabels := by
  change M7.Final.PhysicalLabels
  unfold M7.Final.PhysicalLabels
  exact ⟨M7.GeneratedLabels.pointwise, M7.GeneratedLabels.cache, M7.GeneratedLabels.arrays, M7.GeneratedLabels.witness⟩

theorem M7.Final.presentationextensions : M7.Final.PresentationExtensions := by
  change M7.Final.PresentationExtensions
  unfold M7.Final.PresentationExtensions
  exact ⟨M7.Selection.selector_exact, M7.Selection.selector_strict_dominator, M7.Selection.empty_objectives, M7.ActualPresentation.winning_fiber, M7.ActualPresentation.presentation_sound⟩

theorem M7.Final.replay : M7.Final.Replay := by
  change M7.Final.Replay
  unfold M7.Final.Replay
  exact ⟨M7.FinalReplay.parts,
    M7.FinalReplay.exists_certificate,
    M7.FinalReplay.checked_sets,
    M7.FinalReplay.raw_winners,
    M7.FinalReplay.raw_presentations,
    M7.FinalReplay.physical_labels,
    M7.FinalReplay.invalid_rejection,
    M7.GenerationReplay.generate_checked,
    M7.GenerationReplay.checked_coverage,
    M7.LabelReplay.trace_recover,
    M7.LabelReplay.check_sound,
    M7.LabelReplay.self_check,
    M7.LabelReplay.checked_physical_answer,
    M7.FactorReplay.pool_complete,
    M7.FactorReplay.irreducible_check_exact,
    M7.FactorReplay.factor_check_exact,
    M7.FactorReplay.self_check⟩

theorem M7.Final.resources : M7.Final.Resources := by
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

theorem M7.Final.selector : M7.Final.Selector := by
  change M7.Final.Selector
  unfold M7.Final.Selector
  exact ⟨M7.GlobalQuery.winning_classes,
    M7.FinalSelector.raw_realizable,
    M7.FinalSelector.index_feasible,
    M7.FinalSelector.winner_exact,
    M7.FinalSelector.raw_output,
    M7.FinalSelector.presentation_exact,
    M7.FinalSelector.empty_exact,
    M7.FinalSelector.strict_dominator,
    M7.FinalSelector.invalid_rejection,
    M7.DefaultQuery.sector_modes,
    M7.DefaultQuery.noLogical_policy,
    M7.DefaultQuery.empty_objectives,
    M7.ActualPresentation.four_field_order,
    M7.ActualPresentation.leastAction_spec,
    M7.ActualPresentation.presentation_exact⟩

theorem M7.Final.original_m7 : M7.Final.OriginalM7 := by
  change M7.Final.OriginalM7
  unfold M7.Final.OriginalM7
  exact ⟨M7.Final.actionsignature,
    M7.Final.canonical,
    M7.Final.generation,
    M7.Final.selector,
    M7.Final.physicallabels,
    M7.Final.replay,
    M7.Final.resources,
    M7.Final.presentationextensions⟩
#print axioms M7.Final.actionsignature
#print axioms M7.Final.canonical
#print axioms M7.Final.generation
#print axioms M7.Final.physicallabels
#print axioms M7.Final.presentationextensions
#print axioms M7.Final.replay
#print axioms M7.Final.resources
#print axioms M7.Final.selector
#print axioms M7.Final.original_m7
