import FrozenTarget_c7740198da1ae1f4
theorem M7.ActualOrbit.count_product : QuantumHarnessFrozenTarget := by
  intro N inst c P
  classical
  have hA : M7.ActualOrbit.actionCount c P = M7.OrbitFibers.actionCount (M7.Action.Record N) c P := by
    unfold M7.ActualOrbit.actionCount M7.OrbitFibers.actionCount
    apply congrArg Finset.card
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hD : M7.ActualOrbit.distinctCount c P = M7.OrbitFibers.orbitCount (M7.Action.Record N) c P := by
    unfold M7.ActualOrbit.distinctCount M7.OrbitFibers.orbitCount
    apply congrArg Finset.card
    ext y
    simp only [Finset.mem_filter, M7.ActualOrbit.orbit, M7.OrbitFibers.orbit, Finset.mem_image]
    rfl
  have hS : M7.ActualOrbit.stabilizerCount c = M7.OrbitFibers.stabilizerCount (M7.Action.Record N) c := by
    unfold M7.ActualOrbit.stabilizerCount M7.ActualOrbit.fullStabilizer M7.OrbitFibers.stabilizerCount
    apply congrArg Finset.card
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hA, hD, hS]
  exact M7.OrbitFibers.action_count_product (M7.Action.Record N) (M7.Action.Recipe N) c P
