import FrozenTarget_27b4005764069712
theorem M7.PrefixCompleted.count_completed : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro N w E A B WA WB hN hE hBase
  by_cases hOver : w < A.card ∨ w < B.card
  · rw [M7.PrefixSector.overfull_zero N w E A B WA WB hOver,
      M7.PrefixCompleted.overfull_empty N w E A B WA WB hOver]
    simp
  · have hAw : A.card ≤ w := by omega
    have hBw : B.card ≤ w := by omega
    obtain ⟨hA0, hB0, hAN, hBN, hWAN, hWBN, hDA, hDB⟩ := hBase
    have hOK : M5.ConditionalCount.PrefixOK N w A B WA WB := by
      unfold M5.ConditionalCount.PrefixOK
      aesop
    rw [M7.PrefixSector.exact_sector_count N w E A B WA WB hN hE hOK]
    unfold M7.PrefixCompleted.completed
    rw [Finset.card_image_of_injOn
      (M7.PrefixCompleted.union_injective N w E A B WA WB hDA hDB)]
