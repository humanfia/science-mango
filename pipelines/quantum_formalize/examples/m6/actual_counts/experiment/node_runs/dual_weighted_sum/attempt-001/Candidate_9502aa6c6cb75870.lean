import FrozenTarget_9502aa6c6cb75870
theorem M6.ActualCounts.dual_weighted_sum : QuantumHarnessFrozenTarget := by
  classical
  intro N inst a b ha hb w
  have himage :
      M6.ActualCounts.imageWords
        (fun h : M6.Physical.Block N => M6.Spaces.dualBoundary N
          (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h) =
      M6.Character.subspaceWords (M6.Spaces.D N
        (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) := by
    ext v
    simp [M6.ActualCounts.imageWords, M6.Character.subspaceWords,
      M6.Spaces.D, LinearMap.mem_range]
  have hs := M6.ActualCounts.finite_image_weighted_sum
    (M6.Physical.Block N) (M6.Pinned.Vector (2*N))
    (fun h => M6.Spaces.dualBoundary N
      (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)
    (2 ^ M6.ActualCounts.f N a b)
    (M6.ActualCounts.dual_boundary_fiber_card N a b ha hb) w
  rw [himage] at hs
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hs
