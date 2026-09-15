import FrozenTarget_15a3767ff209c32b
theorem M7.ActualOrbit.count_product : QuantumHarnessFrozenTarget := by
  intro N inst c P
  classical
  have ha : M7.ActualOrbit.actionCount c P = M7.OrbitFibers.actionCount (M7.Action.Record N) c P := by
    unfold M7.ActualOrbit.actionCount M7.OrbitFibers.actionCount
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  have ho : M7.ActualOrbit.distinctCount c P = M7.OrbitFibers.orbitCount (M7.Action.Record N) c P := by
    unfold M7.ActualOrbit.distinctCount M7.OrbitFibers.orbitCount M7.ActualOrbit.orbit M7.OrbitFibers.orbit
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] <;> rfl
  have hs : M7.ActualOrbit.stabilizerCount c = M7.OrbitFibers.stabilizerCount (M7.Action.Record N) c := by
    unfold M7.ActualOrbit.stabilizerCount M7.ActualOrbit.fullStabilizer M7.OrbitFibers.stabilizerCount
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  rw [ha, ho, hs]
  exact M7.OrbitFibers.action_count_product (M7.Action.Record N) (M7.Action.Recipe N) c P
