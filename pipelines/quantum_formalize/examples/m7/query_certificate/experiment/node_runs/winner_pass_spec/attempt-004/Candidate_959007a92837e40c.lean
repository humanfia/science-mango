import FrozenTarget_959007a92837e40c
theorem M7.QueryCertificate.winner_pass_spec : QuantumHarnessFrozenTarget := by
  classical
  intro H N inst q bases W dominator
  simp only [M7.QueryCertificate.winnerPass, M7.QueryCertificate.allOn,
    List.all_eq_true, Finset.mem_toList, Bool.and_eq_true,
    decide_eq_true_eq, Finset.mem_univ, forall_const]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro x
  by_cases hf : M7.GlobalQuery.feasible q bases x
  · by_cases hw : x ∈ W
    · simp [hf, hw]
    · cases hd : dominator x <;> simp [hf, hw, hd]
  · simp [hf]
