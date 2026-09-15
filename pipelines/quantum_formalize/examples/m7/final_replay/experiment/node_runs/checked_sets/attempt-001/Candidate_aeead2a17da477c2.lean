import FrozenTarget_aeead2a17da477c2
theorem M7.FinalReplay.checked_sets : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N w inst q hw hwN c hc
  rcases (M7.FinalReplay.parts N w q c).mp hc with ⟨hv, hg, hf, hb, hl, hq⟩
  exact (M7.QueryCertificate.check_sound _ N q (M7.FinalSelector.family N w q) c.query hq).2
