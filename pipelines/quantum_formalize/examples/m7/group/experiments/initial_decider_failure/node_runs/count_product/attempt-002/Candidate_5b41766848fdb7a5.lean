import FrozenTarget_5b41766848fdb7a5
theorem M7.ActualOrbit.count_product : QuantumHarnessFrozenTarget := by
  classical
  intro N hN c P
  have horbit : M7.ActualOrbit.orbit c = M7.OrbitFibers.orbit (M7.Action.Record N) c := by
    ext y
    simp only [M7.ActualOrbit.orbit, M7.OrbitFibers.orbit, Finset.mem_image]
    rfl
  simpa only [M7.ActualOrbit.actionCount, M7.ActualOrbit.distinctCount,
    M7.ActualOrbit.stabilizerCount, M7.ActualOrbit.fullStabilizer,
    M7.OrbitFibers.actionCount, M7.OrbitFibers.orbitCount,
    M7.OrbitFibers.stabilizerCount, horbit] using
    (M7.OrbitFibers.action_count_product (M7.Action.Record N)
      (M7.Action.Recipe N) c P)
