import FrozenTarget_fe913b5b85838625
theorem M7.FinalReplay.exists_certificate : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q hw hwN hv
  have hE : M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q) := by
    apply M7.QuerySectors.effective_valid <;> assumption
  have hm : (M6.Cyclic.modulus N).Monic := by
    simpa [M6.Cyclic.modulus] using
      (Polynomial.monic_X_pow_sub_C (1 : ZMod 2) (NeZero.ne N))
  obtain ⟨dominator, hd⟩ :=
    (M7.QueryCertificate.check_exact
      (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)) N q
      (M7.FinalSelector.family N w q)
      (M7.GlobalQuery.winners q (M7.FinalSelector.family N w q))
      (M7.QueryCertificate.allPresentations q (M7.FinalSelector.family N w q))).2
      ⟨hv, rfl, rfl⟩
  refine ⟨{
    generation := M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)
    factors := M7.FactorReplay.expected (M6.Cyclic.modulus N)
    labels := fun i => M7.LabelReplay.expected (M7.FinalSelector.family N w q i)
    query := ⟨M7.GlobalQuery.winners q (M7.FinalSelector.family N w q),
      M7.QueryCertificate.allPresentations q (M7.FinalSelector.family N w q), dominator⟩
  }, ?_⟩
  apply (M7.FinalReplay.parts N w q _).2
  refine ⟨hv, ?_, ?_, rfl, ?_, hd⟩
  · apply M7.GenerationReplay.generate_checked <;> assumption
  · exact M7.FactorReplay.self_check (M6.Cyclic.modulus N) hm
  · intro i
    exact M7.LabelReplay.self_check N (M7.FinalSelector.family N w q i)
