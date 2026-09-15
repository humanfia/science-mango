import FrozenTarget_edd2fe18c8e79ed3
theorem M7.QueryCertificate.presentation_pass_spec : QuantumHarnessFrozenTarget := by
  intro H N inst bases W P
  classical
  simp [M7.QueryCertificate.presentationPass, M7.QueryCertificate.allOn,
    List.all_eq_true, M7.QueryCertificate.isLeast] <;> aesop
