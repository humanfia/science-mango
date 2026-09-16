import M8Diagonal

theorem M8.Diagonal.delta_weight : ∀ (N : ℕ) [NeZero N], ∀ j : ZMod N, M6.Physical.weight N (M6.Physical.delta N j) = 1 := by
  intro N inst j
  classical
  change (Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0)).card = 1
  have h : Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0) = {j} := by
    ext i
    by_cases hij : i = j
    · subst i
      simp [M6.Physical.delta]
    · simp [M6.Physical.delta, hij, Ne.symm hij]
  rw [h]
  simp
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ p : M6.Physical.Block N, M8.Diagonal.DeltaNotImage N p → (M6.Flatten.flatten N (M6.Physical.delta N 0, M6.Physical.delta N 0) ∈ M6.Spaces.logicalWords N p p ∧ M6.Pinned.weight (M6.Flatten.flatten N (M6.Physical.delta N 0, M6.Physical.delta N 0)) = 2)
