import FrozenTarget_800451d85a5e8bd4
theorem M6.Final.zero_span_correct : QuantumHarnessFrozenTarget := by
  change M6.Final.ZeroSpanCorrect
  unfold M6.Final.ZeroSpanCorrect
  repeat' constructor
  all_goals intros
  all_goals first
    | solve | exact?
    | (first
        | unfold actualQ
        | unfold M6.actualQ
        | unfold M6.ActualCounts.actualQ
        | unfold M6.ActualTransfer.actualQ
        | unfold M6.Normalize.actualQ
       simp_all [M6.ZeroSpan.boundary_trace_zero,
         M6.ZeroSpan.character_trace_zero, M6.ZeroSpan.signature_one,
         M6.Normalize.divide_scaled])
