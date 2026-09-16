import FrozenTarget_1b56db8d2d050970
theorem M8.Exclusion.span_rejected : QuantumHarnessFrozenTarget := by
  intro N inst w c hw hvalid hF hspan
  apply (M8.Solver.unrecognized_exact N c w hw hvalid).2
  refine ⟨hF, ?_⟩
  apply lt_of_not_ge
  intro hle
  have hd : M8.Discovery.discover c ≠ none :=
    (M8.Solver.discovery_span N c w hw hvalid).2 hle
  rcases (M8.Discovery.complete N c).1 hd with ⟨g, _, hg⟩
  exact (not_lt_of_ge hg) (hspan g)
