import FrozenTarget_1ff2f95dfbcda73f
theorem M7.PrefixSector.exact_sector_count : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB hN hE hPrefix
  unfold M7.PrefixSector.count M7.PrefixSector.completions
  rw [Finset.card_biUnion]
  · rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro F hF
    exact M5.ConditionalCount.exact_completion_C N w F A B WA WB
      hN (hE F hF).1 (hE F hF).2 hPrefix
  · intro F hF G hG hFG
    exact M7.PrefixSector.disjoint_signatures N w F G A B WA WB hFG
