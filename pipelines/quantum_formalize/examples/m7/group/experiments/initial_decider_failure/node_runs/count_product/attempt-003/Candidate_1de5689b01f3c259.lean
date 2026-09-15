import FrozenTarget_1de5689b01f3c259
theorem M7.ActualOrbit.count_product : QuantumHarnessFrozenTarget := by
  intro N inst c P
  classical
  change M7.OrbitFibers.actionCount (M7.Action.Record N) c P =
    M7.OrbitFibers.orbitCount (M7.Action.Record N) c P *
      M7.OrbitFibers.stabilizerCount (M7.Action.Record N) c
  exact M7.OrbitFibers.action_count_product (M7.Action.Record N) (M7.Action.Recipe N) c P
