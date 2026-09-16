import FrozenTarget_e50b9d2a785f3337
theorem M8.CoverageFoundation.coset_direction : QuantumHarnessFrozenTarget := by
  intro N _ A H h
  rcases h with ⟨a, ha⟩
  change AddSubgroup.closure (M7.Connectivity.differences A) ≤ H
  apply (AddSubgroup.closure_le H).2
  rintro d ⟨x, hx, y, hy, rfl⟩
  have hsub := H.sub_mem (ha x hx) (ha y hy)
  simpa only [sub_sub_sub_cancel_right] using hsub
