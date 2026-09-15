import FrozenTarget_12a78f189b6580b0
theorem M7.ActualOrbit.action_partition : QuantumHarnessFrozenTarget := by
  intro N inst c P test
  classical
  have hcount (Q : M7.Action.Recipe N → Prop) :
      M7.ActualOrbit.actionCount c Q =
        M7.OrbitFibers.actionCount (M7.Action.Record N) c Q := by
    unfold M7.ActualOrbit.actionCount M7.OrbitFibers.actionCount
    apply congrArg Finset.card
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  simp only [hcount]
  exact M7.OrbitFibers.action_partition (M7.Action.Record N) (M7.Action.Recipe N) c P test
