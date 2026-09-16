import FrozenTarget_02948cca8ef94ec6
theorem M8.CoverageFoundation.coset_direction : QuantumHarnessFrozenTarget := by
  intro N inst A H h
  rcases h with ⟨a, ha⟩
  change AddSubgroup.closure (M7.Connectivity.differences A) ≤ H
  apply AddSubgroup.closure_le
  intro d hd
  rcases hd with ⟨x, hx, y, hy, rfl⟩
  simpa only [sub_sub_sub_cancel_right] using H.sub_mem (ha x hx) (ha y hy)
