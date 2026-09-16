import FrozenTarget_09ea94288d041ed0
theorem M8.MixedNonproduct.orbit_nonproduct : QuantumHarnessFrozenTarget := by
  intro N inst hN g hprod
  have hp := (M8.MixedNonproduct.product_action N g (M8.MixedFamily.recipe N)).mp hprod
  have hr := (M8.MixedNonproduct.product_rectangular N (M8.MixedFamily.recipe N)).mp hp
  obtain ⟨hab, hzero, hnot⟩ := M8.MixedNonproduct.mixed_obstruction N hN
  exact hnot (hr _ hab _ hzero)
