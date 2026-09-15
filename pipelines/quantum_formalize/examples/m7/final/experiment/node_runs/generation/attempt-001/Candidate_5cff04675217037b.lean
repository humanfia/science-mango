import FrozenTarget_5cff04675217037b
theorem M7.Final.generation : QuantumHarnessFrozenTarget := by
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
