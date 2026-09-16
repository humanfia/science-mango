import FrozenTarget_5d1fabf65b792353
theorem M8.CoverageFoundation.coset_direction : QuantumHarnessFrozenTarget := by
  intro N inst A H hA
  rcases hA with ⟨a, ha⟩
  change AddSubgroup.closure (M7.Connectivity.differences A) ≤ H
  apply AddSubgroup.closure_le
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  have he : x - y = (x - a) - (y - a) := by abel
  rw [he]
  exact H.sub_mem (ha x hx) (ha y hy)
