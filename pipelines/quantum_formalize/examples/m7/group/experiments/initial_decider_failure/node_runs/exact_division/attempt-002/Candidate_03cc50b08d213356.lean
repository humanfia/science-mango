import FrozenTarget_03cc50b08d213356
theorem M7.ActualOrbit.exact_division : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst c P
  classical
  have ha : M7.ActualOrbit.actionCount c P = M7.OrbitFibers.actionCount (M7.Action.Record N) c P := by
    unfold M7.ActualOrbit.actionCount M7.OrbitFibers.actionCount
    apply congrArg Finset.card
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  have hs : M7.ActualOrbit.stabilizerCount c = M7.OrbitFibers.stabilizerCount (M7.Action.Record N) c := by
    unfold M7.ActualOrbit.stabilizerCount M7.ActualOrbit.fullStabilizer M7.OrbitFibers.stabilizerCount
    apply congrArg Finset.card
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  have hd : M7.ActualOrbit.distinctCount c P = M7.OrbitFibers.orbitCount (M7.Action.Record N) c P := by
    unfold M7.ActualOrbit.distinctCount M7.ActualOrbit.orbit M7.OrbitFibers.orbitCount M7.OrbitFibers.orbit
    apply congrArg Finset.card
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] <;> rfl
  rw [ha, hs, hd]
  exact M7.OrbitFibers.orbit_count_div (M7.Action.Record N) (M7.Action.Recipe N) c P
