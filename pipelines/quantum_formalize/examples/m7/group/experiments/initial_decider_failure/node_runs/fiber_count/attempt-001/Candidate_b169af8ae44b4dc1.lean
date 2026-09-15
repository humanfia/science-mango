import FrozenTarget_b169af8ae44b4dc1
theorem M7.ActualOrbit.fiber_count : QuantumHarnessFrozenTarget := by
  intro N inst c y hy
  classical
  change y ∈ M7.OrbitFibers.orbit (M7.Action.Record N) c at hy
  change M7.OrbitFibers.fiberCount (M7.Action.Record N) c y = M7.OrbitFibers.stabilizerCount (M7.Action.Record N) c
  exact M7.OrbitFibers.fiber_count (M7.Action.Record N) (M7.Action.Recipe N) c y hy
