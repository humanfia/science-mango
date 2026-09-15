import FrozenTarget_a278465b291cf5e0
theorem M7.ActualOrbit.count_product : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c P
  simpa only [M7.ActualOrbit.actionCount, M7.ActualOrbit.distinctCount,
    M7.ActualOrbit.stabilizerCount, M7.ActualOrbit.fullStabilizer,
    M7.ActualOrbit.orbit, M7.OrbitFibers.actionCount,
    M7.OrbitFibers.orbitCount, M7.OrbitFibers.stabilizerCount,
    M7.OrbitFibers.orbit] using
    (M7.OrbitFibers.action_count_product (M7.Action.Record N)
      (M7.Action.Recipe N) c P)
