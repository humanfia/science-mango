import FrozenTarget_0ddd724fb369ec61
theorem M6.Final.zero_span_correct : QuantumHarnessFrozenTarget := by
  change M6.Final.ZeroSpanCorrect
  unfold M6.Final.ZeroSpanCorrect
  repeat' first | intro | constructor
  all_goals first
    | solve | exact?
    | first
        | unfold M6.Final.actualQ
        | unfold M6.ActualCounts.actualQ
        | unfold M6.ActualTransfer.actualQ
        | unfold M6.Normalize.actualQ
        | unfold M6.actualQ
        | unfold actualQ
      simp_all [M6.ZeroSpan.boundary_trace_zero,
        M6.ZeroSpan.character_trace_zero, M6.ZeroSpan.signature_one,
        M6.Normalize.divide_scaled]
