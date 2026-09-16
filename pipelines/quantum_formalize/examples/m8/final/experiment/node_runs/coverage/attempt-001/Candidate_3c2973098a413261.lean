import FrozenTarget_3c2973098a413261
theorem M8.Final.coverage : QuantumHarnessFrozenTarget := by
  change M8.Final.AdmittedFamilies
  unfold M8.Final.AdmittedFamilies
  exact ⟨M8.Coverage.p3_physical, M8.Coverage.p3_recognized, M8.Coverage.p4_physical, M8.Coverage.p4_recognized, M8.Coverage.p4_full_multiplicity, M8.Coverage.mixed_recognized⟩
