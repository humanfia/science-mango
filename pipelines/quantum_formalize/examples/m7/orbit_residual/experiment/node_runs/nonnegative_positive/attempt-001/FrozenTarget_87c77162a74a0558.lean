import M7OrbitResidual

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
  ∀ (N : ℕ) [NeZero N], ∀ C bases : Finset (M7.Action.Recipe N), M7.OrbitResidual.Separated bases → 0 ≤ M7.OrbitResidual.subtraction C bases ∧ (0 < M7.OrbitResidual.subtraction C bases ↔ ∃ y ∈ C, y ∉ M7.OrbitResidual.covered bases)
