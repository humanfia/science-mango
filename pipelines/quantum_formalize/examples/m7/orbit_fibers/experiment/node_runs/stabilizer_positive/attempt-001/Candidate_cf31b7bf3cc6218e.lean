import FrozenTarget_cf31b7bf3cc6218e
theorem M7.OrbitFibers.stabilizer_positive : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro G _ _ X _ c
  classical
  unfold M7.OrbitFibers.stabilizerCount
  apply Finset.card_pos.mpr
  refine ⟨(1 : G), ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, one_smul G c⟩
