import FrozenTarget_d08c6842b00339a1
theorem M7.QueryCertificate.presentation_pass_spec : QuantumHarnessFrozenTarget := by
  intro H N inst bases W P
  classical
  simp only [M7.QueryCertificate.presentationPass, M7.QueryCertificate.allOn,
    M7.QueryCertificate.isLeast, Bool.and_eq_true, List.all_eq_true,
    Finset.mem_toList, decide_eq_true_eq]
  constructor
  · rintro ⟨hP, hW⟩ x
    constructor
    · intro hx
      exact hP x hx
    · rintro ⟨hxW, hxLeast⟩
      exact hW x hxW hxLeast
  · intro h
    constructor
    · intro x hx
      exact (h x).mp hx
    · intro x hxW hxLeast
      exact (h x).mpr ⟨hxW, hxLeast⟩
