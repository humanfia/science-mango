import FrozenTarget_6766f90b2933b144
theorem M6.Final.zero_span_correct : QuantumHarnessFrozenTarget := by
  change M6.Final.ZeroSpanCorrect
  unfold M6.Final.ZeroSpanCorrect
  intros
  repeat' apply And.intro
  all_goals first | exact? | (intros; exact?)
