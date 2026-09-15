import FrozenTarget_2e7b89a81952eb72
theorem M7.QueryCertificate.winner_pass_spec : QuantumHarnessFrozenTarget := by
  intro H N inst q bases W dominator
  classical
  simp only [M7.QueryCertificate.winnerPass, M7.QueryCertificate.allOn,
    List.all_eq_true, Finset.mem_toList, Bool.and_eq_true,
    decide_eq_true_eq, Finset.mem_univ, true_implies]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h x hf hn
    have hx := h x
    cases hd : dominator x with
    | none => simp [hf, hn, hd] at hx
    | some y =>
        exact ⟨y, rfl, by simpa [hf, hn, hd] using hx⟩
  · intro h x
    by_cases hc : M7.GlobalQuery.feasible q bases x ∧ x ∉ W
    · obtain ⟨y, hy, hw, hb⟩ := h x hc.1 hc.2
      simp [hc, hy, hw, hb]
    · simp [hc]
