import FrozenTarget_c4ef930a41ec2f74
theorem M8.MixedFamily.valid : QuantumHarnessFrozenTarget := by
  intro N inst hN
  classical
  obtain ⟨hL, hR, h0L, h0R, h1L⟩ := M8.MixedFamily.support_data N hN
  have hf := M8.MixedFamily.full_direction N hN
  change AddSubgroup.closure (M7.Connectivity.differences (M8.MixedFamily.left N)) = ⊤ at hf
  have hc : M7.Connectivity.connected (M8.MixedFamily.recipe N) := by
    change AddSubgroup.closure (M7.Connectivity.differences (M8.MixedFamily.left N) ∪ M7.Connectivity.differences (M8.MixedFamily.right N)) = ⊤
    apply top_unique
    calc
      ⊤ = AddSubgroup.closure (M7.Connectivity.differences (M8.MixedFamily.left N)) := hf.symm
      _ ≤ AddSubgroup.closure (M7.Connectivity.differences (M8.MixedFamily.left N) ∪ M7.Connectivity.differences (M8.MixedFamily.right N)) := AddSubgroup.closure_mono Set.subset_union_left
  simp_all [M8.PhysicalBridge.Valid, M8.MixedFamily.recipe]
