import FrozenTarget_ffccadb8e429c88f
theorem M7.ActualOrbit.distinct_partition : QuantumHarnessFrozenTarget := by
  intro N inst c P test
  classical
  simpa only [M7.ActualOrbit.distinctCount, M7.ActualOrbit.orbit,
    M7.OrbitFibers.orbitCount, M7.OrbitFibers.orbit] using
    (M7.OrbitFibers.orbit_partition (M7.Action.Record N)
      (M7.Action.Recipe N) c P test)
