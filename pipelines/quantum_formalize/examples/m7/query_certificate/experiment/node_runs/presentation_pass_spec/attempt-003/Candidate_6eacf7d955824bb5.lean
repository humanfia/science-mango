import FrozenTarget_6eacf7d955824bb5
theorem M7.QueryCertificate.presentation_pass_spec : QuantumHarnessFrozenTarget := by
  intro H N inst bases W P
  classical
  simp only [M7.QueryCertificate.presentationPass, M7.QueryCertificate.allOn,
    M7.QueryCertificate.isLeast, Bool.and_eq_true, List.all_eq_true, Finset.mem_toList]
  constructor
  · rintro ⟨hP, hW⟩ x
    constructor
    · intro hx
      exact of_decide_eq_true (hP x hx)
    · rintro ⟨hxW, hxLeast⟩
      exact of_decide_eq_true (hW x hxW) hxLeast
  · intro h
    constructor
    · intro x hx
      exact decide_eq_true ((h x).mp hx)
    · intro x hxW
      apply decide_eq_true
      intro hxLeast
      exact (h x).mpr ⟨hxW, hxLeast⟩
