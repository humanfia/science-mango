import FrozenTarget_0a1cffbf3a7be5fa
theorem M7.ActualOrbit.fiber_count : QuantumHarnessFrozenTarget := by
  intro N inst c y hy
  classical
  have hsmul (g : M7.Action.Record N) (x : M7.Action.Recipe N) :
      g • x = M7.Action.act g x := rfl
  have hy' : y ∈ M7.OrbitFibers.orbit (M7.Action.Record N) c := by
    simpa only [M7.OrbitFibers.orbit, M7.ActualOrbit.orbit, hsmul] using hy
  simpa only [M7.OrbitFibers.fiberCount, M7.OrbitFibers.stabilizerCount,
    M7.ActualOrbit.fiberCount, M7.ActualOrbit.stabilizerCount,
    M7.ActualOrbit.fullStabilizer, hsmul] using
    (M7.OrbitFibers.fiber_count (M7.Action.Record N) (M7.Action.Recipe N) c y hy')
