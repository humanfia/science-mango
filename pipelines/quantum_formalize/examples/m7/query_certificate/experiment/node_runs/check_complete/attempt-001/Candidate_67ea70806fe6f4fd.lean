import FrozenTarget_67ea70806fe6f4fd
theorem M7.QueryCertificate.check_complete : QuantumHarnessFrozenTarget := by
  classical
  intro H N inst q bases hvalid
  obtain ⟨dominator, hwin⟩ := M7.QueryCertificate.winner_pass_complete H N q bases
  have hpres : M7.QueryCertificate.presentationPass bases
      (M7.GlobalQuery.winners q bases)
      (M7.QueryCertificate.allPresentations q bases) = true := by
    apply (M7.QueryCertificate.presentation_pass_spec H N bases
      (M7.GlobalQuery.winners q bases)
      (M7.QueryCertificate.allPresentations q bases)).2
    intro x
    simp [M7.QueryCertificate.allPresentations, M7.GlobalQuery.present,
      M7.QueryCertificate.isLeast,
      (M7.ActualPresentation.leastAction_spec N (bases x.1)
        (M7.GlobalQuery.realize bases x)).1,
      M7.GlobalQuery.realize]
  refine ⟨dominator, ?_⟩
  simp [M7.QueryCertificate.check, hvalid, hwin, hpres]
