import FrozenTarget_d345cc1dc548053f
theorem M5.ArithmeticWorkflow.birth_exact : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0 hA
  classical
  unfold M5.ArithmeticWorkflow.birth
  apply M5.BirthSearch.birth_exact _ _ _ _
    (fun N => ∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)
  · intro N hN
    rcases hN with ⟨S, U, hR⟩
    rcases M5.OrderBoundary.signature_lower_bounds N w F S U hF hF0 hR with ⟨hd, hwN, hdeg⟩
    exact ⟨max_le hwN (by omega), hd⟩
  · intro N hlower hd
    have hN : 0 < N := by omega
    exact M5.ArithmeticWorkflow.order_count_iff N w F hN (by omega) hF hF0
  · obtain ⟨S, U, N, E, hE, hbound, hR⟩ :=
      M5.GlobalCriterion.positive_bounded_progression w F hw hF hF0 hA
    refine ⟨N, Nat.le_of_lt hbound, S, U, ?_⟩
    simpa using hR 0
