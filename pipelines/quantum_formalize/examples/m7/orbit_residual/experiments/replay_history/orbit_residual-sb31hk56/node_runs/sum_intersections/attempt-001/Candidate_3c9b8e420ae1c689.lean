import FrozenTarget_3c9b8e420ae1c689
theorem M7.OrbitResidual.sum_intersections : QuantumHarnessFrozenTarget := by
  classical
  intro N inst C bases hsep
  change (∑ c ∈ bases, ((M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)).card) = (C ∩ M7.OrbitResidual.covered bases).card
  have hdisj : bases.PairwiseDisjoint (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)) := by
    intro c hc d hd hcd
    exact (hsep c hc d hd hcd).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hunion : bases.biUnion (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)) = C ∩ M7.OrbitResidual.covered bases := by
    ext y
    simp only [M7.OrbitResidual.covered, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_inter]
    aesop
  rw [← Finset.card_biUnion hdisj, hunion]
