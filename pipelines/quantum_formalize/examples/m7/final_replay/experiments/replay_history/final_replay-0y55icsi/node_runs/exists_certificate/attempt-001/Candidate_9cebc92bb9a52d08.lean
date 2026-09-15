import FrozenTarget_9cebc92bb9a52d08
theorem M7.FinalReplay.exists_certificate : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q hw hwN hv
  obtain ⟨d, hd⟩ := M7.QueryCertificate.check_complete
    (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)) N q
    (M7.FinalSelector.family N w q) hv
  let c : M7.FinalReplay.Certificate N w q :=
    { generation := M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)
      factors := M7.FactorReplay.expected (M6.Cyclic.modulus N)
      labels := fun i => M7.LabelReplay.expected (M7.FinalSelector.family N w q i)
      query := ⟨M7.GlobalQuery.winners q (M7.FinalSelector.family N w q),
        M7.QueryCertificate.allPresentations q (M7.FinalSelector.family N w q), d⟩ }
  refine ⟨c, (M7.FinalReplay.parts N w q c).mpr ?_⟩
  refine ⟨hv, ?_, ?_, rfl, ?_, hd⟩
  · apply M7.GenerationReplay.generate_checked
    apply M7.QuerySectors.effective_valid <;> assumption
  · apply M7.FactorReplay.self_check
    first
    | exact M6.Cyclic.modulus_monic N
    | exact M6.Cyclic.monic_modulus N
    | unfold M6.Cyclic.modulus
      apply Polynomial.monic_X_pow_sub_C
      exact NeZero.ne N
  · intro i
    exact M7.LabelReplay.self_check N (M7.FinalSelector.family N w q i)
