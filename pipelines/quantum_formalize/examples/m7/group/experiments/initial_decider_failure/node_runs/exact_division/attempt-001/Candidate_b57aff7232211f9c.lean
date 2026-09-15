import FrozenTarget_b57aff7232211f9c
theorem M7.ActualOrbit.exact_division : QuantumHarnessFrozenTarget := by
  intro N inst c P
  classical
  simpa only [M7.ActualOrbit.actionCount, M7.ActualOrbit.stabilizerCount,
    M7.ActualOrbit.fullStabilizer, M7.ActualOrbit.distinctCount,
    M7.ActualOrbit.orbit, M7.OrbitFibers.actionCount,
    M7.OrbitFibers.stabilizerCount, M7.OrbitFibers.orbitCount,
    M7.OrbitFibers.orbit] using
    (M7.OrbitFibers.orbit_count_div (M7.Action.Record N) (M7.Action.Recipe N) c P)
