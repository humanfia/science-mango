import FrozenTarget_47d259f44179b1db
theorem M7.RawCoverage.remaining_coverage : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E bases hw hnorm hvalid hremaining c hc
  obtain ⟨q, hq, r, hr, hy⟩ := M7.RawCoverage.raw_anchor N w E c hw hc
  have hcovered : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.covered bases := by
    by_contra hnot
    have hmem : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E) bases :=
      Finset.mem_sdiff.mpr ⟨hy, hnot⟩
    rw [hremaining] at hmem
    simpa using hmem
  have hcanonical := (M7.CanonicalClasses.coverage_iff N bases _ hnorm).mp hcovered
  have hinv : M7.CanonicalOuter.canonical (M7.Action.act (M7.Action.translate (-q) (-r)) c) = M7.CanonicalOuter.canonical c := by
    apply M7.CanonicalOuter.canonical_invariant
  rw [hinv] at hcanonical
  refine ⟨hcanonical, M7.CanonicalOuter.canonical c, hcanonical, ?_⟩
  refine ⟨_, ?_⟩
  apply M7.CanonicalOuter.realizer_inverse
