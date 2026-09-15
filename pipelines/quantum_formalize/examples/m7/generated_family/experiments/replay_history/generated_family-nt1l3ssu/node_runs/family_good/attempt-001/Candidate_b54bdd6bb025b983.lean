import FrozenTarget_b54bdd6bb025b983
theorem M7.GeneratedFamily.family_good : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E hw hwN hE i
  have hm : M7.GeneratedFamily.family N w E i ∈
      (M7.CompactGeneration.generate (N := N) w E).finalBases :=
    (M7.GeneratedFamily.family_range N w E hw hwN hE _).mpr ⟨i, rfl⟩
  have hg : M7.RecoveryInstance.GoodBases w
      (M7.CompactGeneration.generate (N := N) w E).finalBases := by
    have h := M7.CompactCorrectness.generate_exact N w E hE
    tauto
  simp only [M7.RecoveryInstance.GoodBases, M7.CanonicalClasses.Normalized] at hg
  aesop
