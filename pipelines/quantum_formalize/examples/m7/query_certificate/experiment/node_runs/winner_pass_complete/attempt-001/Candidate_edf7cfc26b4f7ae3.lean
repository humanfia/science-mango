import FrozenTarget_edf7cfc26b4f7ae3
theorem M7.QueryCertificate.winner_pass_complete : QuantumHarnessFrozenTarget := by
  classical
  intro H N inst q bases
  have hd : ∀ x : M7.GlobalQuery.Index H N,
      M7.GlobalQuery.feasible q bases x ∧ x ∉ M7.GlobalQuery.winners q bases →
      ∃ y ∈ M7.GlobalQuery.winners q bases, M7.QueryCertificate.strictBetter q bases y x := by
    intro x hx
    exact M7.GlobalQuery.strict_dominator H N q bases x hx.1 hx.2
  let dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N) :=
    fun x => if hx : M7.GlobalQuery.feasible q bases x ∧ x ∉ M7.GlobalQuery.winners q bases
      then some (Classical.choose (hd x hx)) else none
  refine ⟨dominator, ?_⟩
  apply (M7.QueryCertificate.winner_pass_spec H N q bases
    (M7.GlobalQuery.winners q bases) dominator).2
  constructor
  · intro x hx
    exact ((M7.GlobalQuery.winners_exact H N q bases).1 x).1 hx
  · intro x hf hw
    have hx : M7.GlobalQuery.feasible q bases x ∧ x ∉ M7.GlobalQuery.winners q bases := ⟨hf, hw⟩
    refine ⟨Classical.choose (hd x hx), ?_, Classical.choose_spec (hd x hx)⟩
    simp only [dominator, dif_pos hx]
