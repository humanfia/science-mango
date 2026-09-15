import FrozenTarget_2c17a7bcafe59570
theorem M7.FinalReplay.parts : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q c
  by_cases hv : M7.DefaultQuery.valid N q
  · cases hq : M7.QueryCertificate.check q (M7.FinalSelector.family N w q) c.query with
    | error e =>
        simp [M7.FinalReplay.check, hv, hq]
    | ok b =>
        cases b <;>
          simp [M7.FinalReplay.check, hv, hq, M7.QueryCertificate.allOn, Bool.and_eq_true, and_assoc]
  · simp [M7.FinalReplay.check, hv]
