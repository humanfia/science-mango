import FrozenTarget_9cc82435b1df369b
theorem M7.PrefixCompleted.overfull_empty : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB h
  unfold M7.PrefixCompleted.completed
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases (M7.PrefixSector.completion_membership N w E A B WA WB y).mp hy with ⟨F, hF, hy⟩
    rcases h with h | h <;>
      simp_all [M5.ConditionalCount.validCompletions, Nat.not_le_of_lt h]
  · intro hx
    exact False.elim (Finset.not_mem_empty x hx)
