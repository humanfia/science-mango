import FrozenTarget_77533bdb397a710a
theorem M7.PrefixCompleted.overfull_empty : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB h
  unfold M7.PrefixCompleted.completed
  have hempty : M7.PrefixSector.completions N w E A B WA WB = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨F, hF, hx⟩ := (M7.PrefixSector.completion_membership N w E A B WA WB x).mp hx
    rcases h with hA | hB
    · have hA' : ¬ A.card ≤ w := Nat.not_le.mpr hA
      simp_all [M5.ConditionalCount.validCompletions]
    · have hB' : ¬ B.card ≤ w := Nat.not_le.mpr hB
      simp_all [M5.ConditionalCount.validCompletions]
  rw [hempty]
  simp
