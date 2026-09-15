import FrozenTarget_6a4503e653facdd4
theorem M7.OrbitResidual.sum_intersections : QuantumHarnessFrozenTarget := by
  classical
  intro N inst C bases hsep
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
