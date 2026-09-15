import FrozenTarget_0712d8774b5c2bfe
theorem M7.ActualOrbit.distinct_partition : QuantumHarnessFrozenTarget := by
  classical
  intro N _ c P test
  have hcount (Q : M7.Action.Recipe N → Prop) :
      M7.ActualOrbit.distinctCount c Q =
        M7.OrbitFibers.orbitCount (M7.Action.Record N) c Q := by
    unfold M7.ActualOrbit.distinctCount M7.OrbitFibers.orbitCount
    apply congrArg Finset.card
    apply Finset.ext
    intro y
    simp only [Finset.mem_filter, M7.ActualOrbit.orbit,
      M7.OrbitFibers.orbit, Finset.mem_image]
    rfl
  simpa only [hcount] using
    (M7.OrbitFibers.orbit_partition (M7.Action.Record N)
      (M7.Action.Recipe N) c P test)
