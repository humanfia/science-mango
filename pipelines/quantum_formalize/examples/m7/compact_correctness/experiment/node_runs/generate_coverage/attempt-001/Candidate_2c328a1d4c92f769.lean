import FrozenTarget_2c328a1d4c92f769
theorem M7.CompactCorrectness.generate_coverage : QuantumHarnessFrozenTarget := by
  intro N inst w E hE
  have hx := M7.CompactCorrectness.generate_exact N w E hE
  have hc : (M7.CompactGeneration.generate (N := N) w E).finalResidual =
      M7.CompactGeneration.residual w E
        (M7.CompactGeneration.generate (N := N) w E).finalBases [] := by
    simpa only [M7.CompactGeneration.generate] using
      (M7.CompactCorrectness.run_cache N w E ∅
        (M7.CompactGeneration.residual (N := N) w E ∅ []).toNat
        (M7.CompactGeneration.residual (N := N) w E ∅ []) rfl)
  apply (M7.RecoveryInstance.root_zero N w E
    (M7.CompactGeneration.generate (N := N) w E).finalBases hE hx.1).mp
  rw [M7.CompactCorrectness.residual_eq] at hc
  exact hc.symm.trans hx.2.1
