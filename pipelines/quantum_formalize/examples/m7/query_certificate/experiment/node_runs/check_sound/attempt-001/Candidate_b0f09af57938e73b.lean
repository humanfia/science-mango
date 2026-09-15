import FrozenTarget_b0f09af57938e73b
theorem M7.QueryCertificate.check_sound : QuantumHarnessFrozenTarget := by
  intro H N inst q bases certificate hcheck
  classical
  by_cases hv : M7.DefaultQuery.valid N q
  · have hpasses := hcheck
    simp [M7.QueryCertificate.check, hv, Bool.and_eq_true] at hpasses
    have hW : certificate.winners = M7.GlobalQuery.winners q bases :=
      M7.QueryCertificate.winner_pass_sound H N q bases certificate.winners _ hpasses.1
    refine ⟨hv, hW, ?_⟩
    have hP := (M7.QueryCertificate.presentation_pass_spec H N bases
      certificate.winners certificate.presentations).mp hpasses.2
    apply Finset.ext
    intro x
    simpa [M7.QueryCertificate.allPresentations, M7.GlobalQuery.present,
      M7.QueryCertificate.isLeast, hW] using hP x
  · simp [M7.QueryCertificate.check, hv] at hcheck
