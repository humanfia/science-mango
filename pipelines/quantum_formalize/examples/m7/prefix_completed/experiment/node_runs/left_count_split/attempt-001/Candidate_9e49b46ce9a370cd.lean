import FrozenTarget_9e49b46ce9a370cd
theorem M7.PrefixCompleted.left_count_split : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro N w E A B WA WB hN hE hBase i hi
  obtain ⟨hLeft, hRight⟩ :=
    M7.PrefixCompleted.left_children N w E A B WA WB i hi hBase
  rw [M7.PrefixCompleted.count_completed N w E A B WA WB hN hE hBase,
    M7.PrefixCompleted.count_completed N w E A B (WA.erase i) WB hN hE hLeft,
    M7.PrefixCompleted.count_completed N w E (insert i A) B (WA.erase i) WB hN hE hRight]
  rcases hBase with ⟨hA0, hB0, hA, hB, hWA, hWB, hDA, hDB⟩
  rw [M7.PrefixCompleted.left_sets N w E A B WA WB hDA hDB i hi,
    Finset.card_union_of_disjoint
      (M7.PrefixCompleted.left_disjoint N w E A B WA WB hDA hDB i hi),
    Nat.cast_add]
