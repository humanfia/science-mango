import FrozenTarget_3711cdf5e726c018
theorem M7.RawCoverage.remaining_coverage : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro N w inst E bases hw hnorm hvalid hremaining c hc
  obtain ⟨q, hq, r, hr, hy⟩ := M7.RawCoverage.raw_anchor N w E c hw hc
  have hcovered : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.covered bases := by
    by_contra hn
    have hm : M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E) bases := by
      change _ ∈ M7.RawCoverage.rootCompleted N w E \ M7.OrbitResidual.covered bases
      exact Finset.mem_sdiff.mpr ⟨hy, hn⟩
    rw [hremaining] at hm
    exact Finset.not_mem_empty _ hm
  have hcanonical := (M7.CanonicalClasses.coverage_iff N bases _ hnorm).mp hcovered
  have hinv : M7.CanonicalOuter.canonical (M7.Action.act (M7.Action.translate (-q) (-r)) c) = M7.CanonicalOuter.canonical c := by
    first
    | exact M7.CanonicalOuter.canonical_invariant N c (M7.Action.translate (-q) (-r))
    | exact M7.CanonicalOuter.canonical_invariant N (M7.Action.translate (-q) (-r)) c
    | exact M7.CanonicalOuter.canonical_invariant c (M7.Action.translate (-q) (-r))
  rw [hinv] at hcanonical
  refine ⟨hcanonical, M7.CanonicalOuter.canonical c, hcanonical, ?_⟩
  refine ⟨_, ?_⟩
  first
  | exact M7.CanonicalOuter.realizer_inverse N c
  | exact M7.CanonicalOuter.realizer_inverse c
