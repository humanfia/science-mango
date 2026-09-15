import FrozenTarget_df19bcd47a464454
theorem M7.PrefixSector.count_nonnegative : QuantumHarnessFrozenTarget := by
  intro N w E A B WA WB hN hE hPrefix
  classical
  unfold M7.PrefixSector.count
  apply Finset.sum_nonneg
  intro F hF
  exact (M5.ConditionalCount.completion_nonnegative_and_exists
    N w F A B WA WB hN (hE F hF).1 (hE F hF).2 hPrefix).1
