import FrozenTarget_e185eae85f558ae1
theorem M5.ConditionalCount.completion_nonnegative_and_exists : QuantumHarnessFrozenTarget := by
  intro N w F A B WA WB hN hF hFN hprefix
  rw [M5.ConditionalCount.exact_completion_C N w F A B WA WB hN hF hFN hprefix]
  constructor
  · positivity
  · exact_mod_cast (Finset.card_pos :
      0 < (M5.ConditionalCount.validCompletions N w F A B WA WB).card ↔
        (M5.ConditionalCount.validCompletions N w F A B WA WB).Nonempty)
