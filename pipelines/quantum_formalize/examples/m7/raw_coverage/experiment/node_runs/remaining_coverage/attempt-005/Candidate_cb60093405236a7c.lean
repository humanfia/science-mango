import FrozenTarget_cb60093405236a7c
theorem M7.RawCoverage.remaining_coverage : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E bases hw hnorm hvalid hempty c hc
  obtain ⟨q, hq, r, hr, hy⟩ := M7.RawCoverage.raw_anchor N w E c hw hc
  have hcovered : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.covered bases := by
    by_contra hn
    have hmem : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E) bases := by
      exact Finset.mem_sdiff.mpr ⟨hy, hn⟩
    rw [hempty] at hmem
    simp at hmem
  have hcanon := (M7.CanonicalClasses.coverage_iff N bases _ hnorm).mp hcovered
  have hb : M7.CanonicalOuter.canonical c ∈ bases := by
    simpa only [M7.CanonicalOuter.canonical_invariant] using hcanon
  refine ⟨hb, M7.CanonicalOuter.canonical c, hb, ?_⟩
  first
  | exact ⟨_, M7.CanonicalOuter.realizer_inverse N c⟩
  | exact ⟨_, M7.CanonicalOuter.realizer_inverse c⟩
