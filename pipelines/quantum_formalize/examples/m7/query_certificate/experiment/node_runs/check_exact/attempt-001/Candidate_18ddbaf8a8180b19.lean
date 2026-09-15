import FrozenTarget_18ddbaf8a8180b19
theorem M7.QueryCertificate.check_exact : QuantumHarnessFrozenTarget := by
  intro H N inst q bases W P
  constructor
  · rintro ⟨dominator, hcheck⟩
    exact M7.QueryCertificate.check_sound H N q bases
      (⟨W, P, dominator⟩ : M7.QueryCertificate.Certificate H N) hcheck
  · rintro ⟨hvalid, hW, hP⟩
    rw [hW, hP]
    exact M7.QueryCertificate.check_complete H N q bases hvalid
