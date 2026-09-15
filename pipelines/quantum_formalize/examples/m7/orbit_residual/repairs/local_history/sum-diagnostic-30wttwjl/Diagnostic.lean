import M7OrbitResidual
set_option pp.all true
example : ∀ (N : ℕ) [NeZero N], ∀ C bases : Finset (M7.Action.Recipe N), M7.OrbitResidual.Separated bases → (∑ c ∈ bases, M7.ActualOrbit.distinctCount c (fun y => y ∈ C)) = (C ∩ M7.OrbitResidual.covered bases).card := by
  classical
  intro N inst C bases hsep
  unfold M7.ActualOrbit.distinctCount M7.OrbitResidual.covered
  have hunion : bases.biUnion (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)) = C ∩ bases.biUnion M7.ActualOrbit.orbit := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_inter]
    aesop
  rw [← hunion]
  symm
  have hd : (↑bases : Set (M7.Action.Recipe N)).PairwiseDisjoint (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)) := by
    intro c hc d hd hcd
    exact (hsep c hc d hd hcd).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard := Finset.card_biUnion hd
  exact hcard
