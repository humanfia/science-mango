import FrozenTarget_bea92c595c3d0dfb
theorem M8.CoverageFoundation.coset_direction : QuantumHarnessFrozenTarget := by
  intro N inst A H h
  rcases h with ⟨a, ha⟩
  change AddSubgroup.closure (M7.Connectivity.differences A) ≤ H
  apply AddSubgroup.closure_le.mpr
  intro d hd
  rcases hd with ⟨x, hx, y, hy, rfl⟩
  have hxy := H.sub_mem (ha x hx) (ha y hy)
  simpa only [sub_sub_sub_cancel_right] using hxy
