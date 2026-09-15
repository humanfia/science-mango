import FrozenTarget_b6abbb88f88136a6
theorem M6.Final.zero_span_correct : QuantumHarnessFrozenTarget := by
  change M6.Final.ZeroSpanCorrect
  unfold M6.Final.ZeroSpanCorrect
  intros
  repeat' apply And.intro
  all_goals intros
  all_goals first
    | exact?
    | (simp_all [M6.Final.Admissible, M6.Final.actualQ,
        M6.ZeroSpan.boundary_trace_zero, M6.ZeroSpan.character_trace_zero,
        M6.ZeroSpan.signature_one, M6.Normalize.divide_scaled])
