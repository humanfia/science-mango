import FrozenTarget_cd1a7a09a765c416
theorem M7.ActualOrbit.fiber_count : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c y hy
  have hsmul (g : M7.Action.Record N) : g • c = M7.Action.act g c := rfl
  have hy' : y ∈ M7.OrbitFibers.orbit (M7.Action.Record N) c := by
    simpa only [M7.ActualOrbit.orbit, M7.OrbitFibers.orbit, hsmul] using hy
  have h := M7.OrbitFibers.fiber_count (M7.Action.Record N) (M7.Action.Recipe N) c y hy'
  simpa only [M7.ActualOrbit.fiberCount, M7.ActualOrbit.stabilizerCount,
    M7.ActualOrbit.fullStabilizer, M7.OrbitFibers.fiberCount,
    M7.OrbitFibers.stabilizerCount, hsmul] using h
