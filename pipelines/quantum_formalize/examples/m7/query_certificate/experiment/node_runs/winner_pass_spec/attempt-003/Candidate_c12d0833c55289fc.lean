import FrozenTarget_c12d0833c55289fc
theorem M7.QueryCertificate.winner_pass_spec : QuantumHarnessFrozenTarget := by
  intro H N _ q bases W dominator
  classical
  unfold M7.QueryCertificate.winnerPass M7.QueryCertificate.allOn
  simp only [Bool.and_eq_true, List.all_eq_true, Finset.mem_toList,
    Finset.mem_univ, forall_const, decide_eq_true_eq]
  apply and_congr
  · rfl
  · apply forall_congr
    intro x
    by_cases hf : M7.GlobalQuery.feasible q bases x <;>
      by_cases hw : x ∈ W <;>
      cases hd : dominator x <;>
      simp [hf, hw, hd, Bool.and_eq_true, decide_eq_true_eq]
