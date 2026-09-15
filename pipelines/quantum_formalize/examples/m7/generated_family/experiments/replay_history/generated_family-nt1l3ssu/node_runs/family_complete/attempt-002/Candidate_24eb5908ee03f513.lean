import FrozenTarget_24eb5908ee03f513
theorem M7.GeneratedFamily.family_complete : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E hw hwN hE c
  have hcomp : ∀ (g h : M7.Action.Record N) (b : M7.Action.Recipe N),
      M7.Action.act (M7.Action.compose g h) b = M7.Action.act g (M7.Action.act h b) := by
    intro g h b
    exact?
  have hinv : ∀ (g : M7.Action.Record N) (b : M7.Action.Recipe N),
      M7.Action.act (M7.Action.inverse g) (M7.Action.act g b) = b := by
    intro g b
    exact?
  constructor
  · rintro ⟨i, g, rfl⟩
    refine ⟨M7.PrefixOrbit.class_action N w _ g
      (M7.GeneratedFamily.family_good N w E hw hwN hE i).1, ?_⟩
    obtain ⟨h, hh⟩ := M7.GeneratedFamily.family_meets N w E hw hwN hE i
    refine ⟨M7.Action.compose h (M7.Action.inverse g), ?_⟩
    simpa only [hcomp, hinv] using hh
  · rintro ⟨hc, g, hg⟩
    have hex := M7.CompactCorrectness.generate_exact N w E hE
    have hgood : M7.RecoveryInstance.GoodBases w
        (M7.CompactGeneration.generate (N := N) w E).finalBases := hex.1
    have hnorm : M7.CanonicalClasses.Normalized
        (M7.CompactGeneration.generate (N := N) w E).finalBases := by
      unfold M7.RecoveryInstance.GoodBases at hgood
      tauto
    have hvalid : ∀ b ∈ (M7.CompactGeneration.generate (N := N) w E).finalBases,
        M7.PrefixOrbit.ClassValid w b := by
      unfold M7.RecoveryInstance.GoodBases at hgood
      tauto
    have hsub : M7.RawCoverage.rootCompleted N w E ⊆
        M7.OrbitResidual.covered (M7.CompactGeneration.generate (N := N) w E).finalBases := by
      intro y hy
      exact M7.CompactCorrectness.generate_coverage N w E hE y hy
    have hempty : M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E)
        (M7.CompactGeneration.generate (N := N) w E).finalBases = ∅ := by
      simpa only [M7.OrbitResidual.remaining] using
        (Finset.sdiff_eq_empty_iff_subset.mpr hsub)
    have hq : M7.RawCoverage.Queried w E (M7.Action.act g c) :=
      ⟨M7.PrefixOrbit.class_action N w c g hc, hg⟩
    obtain ⟨b, hb, h, hh⟩ :=
      (M7.RawCoverage.remaining_coverage N w E _ hw hnorm hvalid hempty
        (M7.Action.act g c) hq).2
    obtain ⟨i, hi⟩ := (M7.GeneratedFamily.family_range N w E hw hwN hE b).mp hb
    refine ⟨i, M7.Action.compose (M7.Action.inverse g) h, ?_⟩
    rw [hi, hcomp, hh, hinv]
