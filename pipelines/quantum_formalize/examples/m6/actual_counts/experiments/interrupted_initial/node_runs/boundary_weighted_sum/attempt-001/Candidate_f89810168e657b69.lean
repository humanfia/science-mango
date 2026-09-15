import FrozenTarget_f89810168e657b69
theorem M6.ActualCounts.boundary_weighted_sum : QuantumHarnessFrozenTarget := by
  classical
  intro N inst a b ha hb w
  have himage :
      M6.ActualCounts.imageWords (fun h : M6.Physical.Block N =>
        M6.Spaces.boundary N (M6.Coordinates.coefficients N a)
          (M6.Coordinates.coefficients N b) h) =
      M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a)
        (M6.Coordinates.coefficients N b) := by
    ext v
    simp [M6.ActualCounts.imageWords, M6.Spaces.boundary_words_iff,
      M6.Spaces.boundary_eval]
  have hs := M6.ActualCounts.finite_image_weighted_sum
    (M6.Physical.Block N) (M6.Pinned.Vector (2*N))
    (fun h => M6.Spaces.boundary N (M6.Coordinates.coefficients N a)
      (M6.Coordinates.coefficients N b) h)
    (2 ^ M6.ActualCounts.f N a b)
    (M6.ActualCounts.boundary_fiber_card N a b ha hb) w
  simpa [himage] using hs
