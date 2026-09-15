import FrozenTarget_7a4fb88090cf9985
theorem M7.QueryCertificate.invalid_rule : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases certificate
  classical
  by_cases h : M7.DefaultQuery.valid N q
  <;> simp [M7.QueryCertificate.check, h]
