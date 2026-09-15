import FrozenTarget_79a5a18e0190359f
theorem M7.ActualOrbit.stabilizer_positive : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), 0 < M7.ActualOrbit.stabilizerCount c
  intro N inst c
  classical
  have h := M7.OrbitFibers.stabilizer_positive (M7.Action.Record N) (M7.Action.Recipe N) c
  have heq : M7.ActualOrbit.stabilizerCount c = M7.OrbitFibers.stabilizerCount (M7.Action.Record N) c := by
    unfold M7.ActualOrbit.stabilizerCount M7.ActualOrbit.fullStabilizer M7.OrbitFibers.stabilizerCount
    apply congrArg Finset.card
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  rw [heq]
  exact h
