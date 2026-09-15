import FrozenTarget_14fbd2854c669f73
theorem M7.ActualOrbit.fiber_count : QuantumHarnessFrozenTarget := by
  intro N inst c y hy
  classical
  have hy' : y ∈ M7.OrbitFibers.orbit (M7.Action.Record N) c := by
    simpa only [M7.ActualOrbit.orbit, M7.OrbitFibers.orbit,
      Finset.mem_image, Finset.mem_univ, true_and] using hy
  have h := M7.OrbitFibers.fiber_count (M7.Action.Record N)
    (M7.Action.Recipe N) c y hy'
  convert h using 1
  · unfold M7.ActualOrbit.fiberCount M7.OrbitFibers.fiberCount
    congr 1
    ext g
    simp only [Finset.mem_filter]
  · unfold M7.ActualOrbit.stabilizerCount M7.ActualOrbit.fullStabilizer
      M7.OrbitFibers.stabilizerCount
    congr 1
    ext g
    simp only [Finset.mem_filter]
