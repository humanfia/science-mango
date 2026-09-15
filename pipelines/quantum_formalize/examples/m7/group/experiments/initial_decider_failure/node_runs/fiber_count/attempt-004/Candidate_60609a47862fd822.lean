import FrozenTarget_60609a47862fd822
theorem M7.ActualOrbit.fiber_count : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c y hy
  have hy' : y ∈ M7.OrbitFibers.orbit (M7.Action.Record N) c := by
    simpa only [M7.ActualOrbit.orbit, M7.OrbitFibers.orbit, Finset.mem_image] using hy
  have h := M7.OrbitFibers.fiber_count (M7.Action.Record N) (M7.Action.Recipe N) c y hy'
  calc
    M7.ActualOrbit.fiberCount c y = M7.OrbitFibers.fiberCount (M7.Action.Record N) c y := by
      unfold M7.ActualOrbit.fiberCount M7.OrbitFibers.fiberCount
      congr 1 <;> ext g <;> simp only [Finset.mem_filter] <;> rfl
    _ = M7.OrbitFibers.stabilizerCount (M7.Action.Record N) c := h
    _ = M7.ActualOrbit.stabilizerCount c := by
      unfold M7.OrbitFibers.stabilizerCount M7.ActualOrbit.stabilizerCount M7.ActualOrbit.fullStabilizer
      congr 1 <;> ext g <;> simp only [Finset.mem_filter] <;> rfl
