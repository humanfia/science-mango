import FrozenTarget_f32af829afb5f429
theorem M7.QueryCertificate.winner_pass_spec : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases W dominator
  classical
  unfold M7.QueryCertificate.winnerPass M7.QueryCertificate.allOn
  simp only [List.all_eq_true, Finset.mem_toList, Finset.mem_univ,
    forall_const, Bool.and_eq_true, decide_eq_true_eq]
  apply and_congr
  · simp
  · apply forall_congr
    intro x
    by_cases hf : M7.GlobalQuery.feasible q bases x <;>
      by_cases hw : x ∈ W <;>
      cases hd : dominator x <;>
      simp [hf, hw, hd, Bool.and_eq_true]
