import FrozenTarget_18a6b3f68cdfce97
theorem M7.QueryCertificate.presentation_pass_spec : QuantumHarnessFrozenTarget := by
  intro H N inst bases W P
  classical
  simp only [M7.QueryCertificate.presentationPass, M7.QueryCertificate.allOn,
    Bool.and_eq_true, List.all_eq_true, Finset.mem_toList, decide_eq_true_eq]
  change ((∀ x, x ∈ P → x ∈ W ∧ M7.QueryCertificate.isLeast bases x) ∧
    (∀ x, x ∈ W → M7.QueryCertificate.isLeast bases x → x ∈ P)) ↔
    ∀ x, x ∈ P ↔ x ∈ W ∧ M7.QueryCertificate.isLeast bases x
  constructor
  · rintro ⟨hP, hW⟩ x
    exact ⟨hP x, fun h => hW x h.1 h.2⟩
  · intro h
    constructor
    · intro x hx
      exact (h x).mp hx
    · intro x hx hl
      exact (h x).mpr ⟨hx, hl⟩
