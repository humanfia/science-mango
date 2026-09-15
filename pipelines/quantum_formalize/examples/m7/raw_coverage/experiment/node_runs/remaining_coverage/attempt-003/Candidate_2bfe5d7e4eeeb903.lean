import FrozenTarget_2bfe5d7e4eeeb903
theorem M7.RawCoverage.remaining_coverage : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E bases hw hnorm hvalid hremaining c hc
  obtain ⟨q, hq, r, hr, hy⟩ := M7.RawCoverage.raw_anchor N w E c hw hc
  have hcovered : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.covered bases := by
    by_contra hn
    have hmem : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E) bases := Finset.mem_sdiff.mpr ⟨hy, hn⟩
    rw [hremaining] at hmem
    exact Finset.not_mem_empty _ hmem
  have hcanonical : M7.CanonicalOuter.canonical c ∈ bases := by
    have h := (M7.CanonicalClasses.coverage_iff N bases _ hnorm).mp hcovered
    simpa only [M7.CanonicalOuter.canonical_invariant] using h
  refine ⟨hcanonical, ?_⟩
  have hcCovered := (M7.CanonicalClasses.coverage_iff N bases c hnorm).mpr hcanonical
  obtain ⟨b, hb, hcb⟩ := (M7.OrbitResidual.covered_membership N bases c).mp hcCovered
  refine ⟨b, hb, ?_⟩
  simpa [M7.ActualOrbit.orbit] using hcb
