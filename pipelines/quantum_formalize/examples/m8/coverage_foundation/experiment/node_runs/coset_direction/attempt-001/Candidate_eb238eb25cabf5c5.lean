import FrozenTarget_eb238eb25cabf5c5
theorem M8.CoverageFoundation.coset_direction : QuantumHarnessFrozenTarget := by
  intro N inst A H hA
  rcases hA with ⟨a, ha⟩
  change AddSubgroup.closure (M7.Connectivity.differences A) ≤ H
  apply (AddSubgroup.closure_le H).2
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  change x - y ∈ H
  have he : x - y = (x - a) - (y - a) := by abel
  rw [he]
  exact H.sub_mem (ha x hx) (ha y hy)
