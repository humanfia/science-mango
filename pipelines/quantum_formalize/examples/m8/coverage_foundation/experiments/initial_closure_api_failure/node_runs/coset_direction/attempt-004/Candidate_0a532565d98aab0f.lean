import FrozenTarget_0a532565d98aab0f
theorem M8.CoverageFoundation.coset_direction : QuantumHarnessFrozenTarget := by
  intro N inst A H h
  rcases h with ⟨a, ha⟩
  change AddSubgroup.closure (M7.Connectivity.differences A) ≤ H
  apply AddSubgroup.closure_le.mpr
  rintro z ⟨x, hx, y, hy, rfl⟩
  change x - y ∈ H
  have he : x - y = (x - a) - (y - a) := by ring
  rw [he]
  exact H.sub_mem (ha x hx) (ha y hy)
