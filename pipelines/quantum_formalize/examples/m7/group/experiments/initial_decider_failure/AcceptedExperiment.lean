import M7ActualOrbit

theorem M7.ActualOrbit.action_partition : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (P : M7.Action.Recipe N → Prop) (test : M7.Action.Recipe N → Bool), M7.ActualOrbit.actionCount c P = M7.ActualOrbit.actionCount c (fun y => P y ∧ test y = false) + M7.ActualOrbit.actionCount c (fun y => P y ∧ test y = true) := by
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

theorem M7.ActualOrbit.distinct_partition : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ (P : M7.Action.Recipe N → Prop) (test : M7.Action.Recipe N → Bool), M7.ActualOrbit.distinctCount c P = M7.ActualOrbit.distinctCount c (fun y => P y ∧ test y = false) + M7.ActualOrbit.distinctCount c (fun y => P y ∧ test y = true) := by
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

theorem M7.ActualOrbit.exact_division : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ P : M7.Action.Recipe N → Prop, M7.ActualOrbit.actionCount c P / M7.ActualOrbit.stabilizerCount c = M7.ActualOrbit.distinctCount c P ∧ M7.ActualOrbit.stabilizerCount c ∣ M7.ActualOrbit.actionCount c P := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ P : M7.Action.Recipe N → Prop, M7.ActualOrbit.actionCount c P / M7.ActualOrbit.stabilizerCount c = M7.ActualOrbit.distinctCount c P ∧ M7.ActualOrbit.stabilizerCount c ∣ M7.ActualOrbit.actionCount c P
  )
  change QuantumHarnessFrozenTarget
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

theorem M7.ActualOrbit.stabilizer_positive : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), 0 < M7.ActualOrbit.stabilizerCount c := by
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
#print axioms M7.ActualOrbit.action_partition
#print axioms M7.ActualOrbit.distinct_partition
#print axioms M7.ActualOrbit.exact_division
#print axioms M7.ActualOrbit.stabilizer_positive
