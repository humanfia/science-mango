import FrozenTarget_20518a35ee937bd4
theorem M7.OrbitResidual.sum_intersections : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N inst C bases hsep
    have hcount (c : M7.Action.Recipe N) :
        M7.ActualOrbit.distinctCount c (fun y => y ∈ C) =
          ((M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)).card := by
      unfold M7.ActualOrbit.distinctCount
      congr 1
      ext y
      simp [M7.ActualOrbit.orbit, M7.OrbitFibers.orbitCount,
        M7.OrbitFibers.orbit] <;> aesop
    have hd : (bases : Set (M7.Action.Recipe N)).PairwiseDisjoint
        (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)) := by
      intro c hc d hd hcd
      exact (hsep c hc d hd hcd).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hu : bases.biUnion
        (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)) =
        C ∩ M7.OrbitResidual.covered bases := by
      ext y
      simp only [M7.OrbitResidual.covered, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_inter]
      aesop
    simp_rw [hcount]
    rw [← hu]
    exact (Finset.card_biUnion hd).symm
