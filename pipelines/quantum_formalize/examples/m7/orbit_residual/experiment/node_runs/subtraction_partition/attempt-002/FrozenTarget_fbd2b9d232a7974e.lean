import M7OrbitResidual

theorem M7.OrbitResidual.remaining_partition : ∀ (N : ℕ) [NeZero N], ∀ C0 C1 bases : Finset (M7.Action.Recipe N), M7.OrbitResidual.remaining (C0 ∪ C1) bases = M7.OrbitResidual.remaining C0 bases ∪ M7.OrbitResidual.remaining C1 bases := by
  classical
  intro N inst C0 C1 bases
  unfold M7.OrbitResidual.remaining
  apply Finset.ext
  intro x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h0 | h1, h⟩
    · exact Or.inl ⟨h0, h⟩
    · exact Or.inr ⟨h1, h⟩
  · rintro (⟨h0, h⟩ | ⟨h1, h⟩)
    · exact ⟨Or.inl h0, h⟩
    · exact ⟨Or.inr h1, h⟩

theorem M7.OrbitResidual.sum_intersections : ∀ (N : ℕ) [NeZero N], ∀ C bases : Finset (M7.Action.Recipe N), M7.OrbitResidual.Separated bases → (∑ c ∈ bases, M7.ActualOrbit.distinctCount c (fun y => y ∈ C)) = (C ∩ M7.OrbitResidual.covered bases).card := by
  classical
  intro N inst C bases hsep
  letI : DecidablePred (fun y : M7.Action.Recipe N => y ∈ C) := fun _ => Classical.propDecidable _
  unfold M7.ActualOrbit.distinctCount M7.OrbitResidual.covered
  have hunion : bases.biUnion (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)) = C ∩ bases.biUnion M7.ActualOrbit.orbit := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_inter]
    aesop
  rw [← hunion]
  symm
  apply Finset.card_biUnion (s := bases) (t := fun c : M7.Action.Recipe N => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C))
  intro c hc d hd hcd
  exact (hsep c hc d hd hcd).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem M7.OrbitResidual.subtraction_card : ∀ (N : ℕ) [NeZero N], ∀ C bases : Finset (M7.Action.Recipe N), M7.OrbitResidual.Separated bases → M7.OrbitResidual.subtraction C bases = (M7.OrbitResidual.remaining C bases).card := by
  intro N inst C bases hsep
  classical
  have hsum := congrArg (fun n : ℕ => (n : ℤ))
    (M7.OrbitResidual.sum_intersections N C bases hsep)
  simp only [Nat.cast_sum] at hsum
  unfold M7.OrbitResidual.subtraction M7.OrbitResidual.remaining
  rw [hsum]
  have hcard :
      ((C \ M7.OrbitResidual.covered bases).card : ℤ) +
        ((C ∩ M7.OrbitResidual.covered bases).card : ℤ) = (C.card : ℤ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter C (M7.OrbitResidual.covered bases)
  omega
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ C0 C1 bases : Finset (M7.Action.Recipe N), M7.OrbitResidual.Separated bases → Disjoint C0 C1 → M7.OrbitResidual.subtraction (C0 ∪ C1) bases = M7.OrbitResidual.subtraction C0 bases + M7.OrbitResidual.subtraction C1 bases
