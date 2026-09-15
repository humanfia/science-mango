import FrozenTarget_c4a1d7960bb098c1
theorem M6.Final.fixed_span_correct : QuantumHarnessFrozenTarget := by
  change M6.Final.FixedSpanCorrect
  unfold M6.Final.FixedSpanCorrect
   aesop (add safe apply M6.FixedSpan.distance_improvement M6.FixedSpan.witness_improvement M6.FixedSpan.nontrivial_family)
