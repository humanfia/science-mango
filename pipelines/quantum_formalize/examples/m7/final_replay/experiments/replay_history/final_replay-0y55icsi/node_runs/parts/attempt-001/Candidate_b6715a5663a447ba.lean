import FrozenTarget_b6715a5663a447ba
theorem M7.FinalReplay.parts : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst q c
  by_cases hv : M7.DefaultQuery.valid N q
  · cases hq : M7.QueryCertificate.check q (M7.FinalSelector.family N w q) c.query with
    | error e =>
        simp [M7.FinalReplay.check, hv, hq]
    | ok b =>
        cases b <;>
          simp [M7.FinalReplay.check, hv, hq, M7.QueryCertificate.allOn_spec, and_assoc]
  · simp [M7.FinalReplay.check, hv]
