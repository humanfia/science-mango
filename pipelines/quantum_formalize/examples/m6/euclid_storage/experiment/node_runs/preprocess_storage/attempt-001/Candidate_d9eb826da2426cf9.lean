import FrozenTarget_d9eb826da2426cf9
theorem M6.EuclidStorage.preprocess_storage : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N a b M ha hb hM
  exact ⟨M6.EuclidStorage.preprocess_refines a b M,
    M6.EuclidStorage.preprocess_safe N a b M ha hb hM,
    (M6.EuclidStorage.layout_bound N).2.2⟩
