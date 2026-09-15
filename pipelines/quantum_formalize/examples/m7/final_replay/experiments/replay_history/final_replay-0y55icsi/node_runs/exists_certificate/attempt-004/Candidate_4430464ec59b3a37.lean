import FrozenTarget_4430464ec59b3a37
theorem M7.FinalReplay.exists_certificate : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q hw hwN hq
  have hE : M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q) := by
    apply M7.QuerySectors.effective_valid <;> assumption
  have hm : (M6.Cyclic.modulus N).Monic := by
    have hn : -(1 : ZMod 2) = 1 := by decide
    simpa [M6.Cyclic.modulus, sub_eq_add_neg, hn] using
      (Polynomial.monic_X_pow_sub_C (1 : ZMod 2) (NeZero.ne N))
  obtain ⟨d, hd⟩ := (M7.QueryCertificate.check_exact
    (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)) N q
    (M7.FinalSelector.family N w q)
    (M7.GlobalQuery.winners q (M7.FinalSelector.family N w q))
    (M7.QueryCertificate.allPresentations q (M7.FinalSelector.family N w q))).mpr
    ⟨hq, rfl, rfl⟩
  let c : M7.FinalReplay.Certificate N w q :=
    { generation := M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)
      factors := M7.FactorReplay.expected (M6.Cyclic.modulus N)
      labels := fun i => M7.LabelReplay.expected (M7.FinalSelector.family N w q i)
      query := ⟨M7.GlobalQuery.winners q (M7.FinalSelector.family N w q),
        M7.QueryCertificate.allPresentations q (M7.FinalSelector.family N w q), d⟩ }
  refine ⟨c, (M7.FinalReplay.parts N w q c).mpr ?_⟩
  refine ⟨hq, ?_, ?_, rfl, ?_, hd⟩
  · exact M7.GenerationReplay.generate_checked N w (M7.QuerySectors.effective N q) hE
  · exact M7.FactorReplay.self_check (M6.Cyclic.modulus N) hm
  · intro i
    exact M7.LabelReplay.self_check N (M7.FinalSelector.family N w q i)
