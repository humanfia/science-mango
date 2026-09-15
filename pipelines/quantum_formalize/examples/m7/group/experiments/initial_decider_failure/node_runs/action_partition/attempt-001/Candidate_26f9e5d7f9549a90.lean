import FrozenTarget_26f9e5d7f9549a90
theorem M7.ActualOrbit.action_partition : QuantumHarnessFrozenTarget := by
  intro N inst c P test
  classical
  simpa only [M7.ActualOrbit.actionCount, M7.OrbitFibers.actionCount] using
    (M7.OrbitFibers.action_partition (M7.Action.Record N) (M7.Action.Recipe N) c P test)
