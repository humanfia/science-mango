import FrozenTarget_80af4429fa701766
theorem M7.OrbitResidual.sum_intersections : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N inst C bases hsep
    have hcount (c : M7.Action.Recipe N) :
        M7.ActualOrbit.distinctCount c (fun y => y ∈ C) =
          ((M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)).card := by
      simp [M7.ActualOrbit.distinctCount, M7.ActualOrbit.orbit,
        M7.OrbitFibers.orbitCount, M7.OrbitFibers.orbit, Finset.filter_image]
    have hd : (bases : Set (M7.Action.Recipe N)).PairwiseDisjoint
        (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)) := by
      intro c hc d hd hne
      apply Finset.disjoint_left.mpr
      intro y hy hz
      exact Finset.disjoint_left.mp (hsep c hc d hd hne)
        (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hz).1
    have hu :
        bases.biUnion (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)) =
          C ∩ M7.OrbitResidual.covered bases := by
      ext y
      simp only [M7.OrbitResidual.covered, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_inter]
      aesop
    simp_rw [hcount]
    rw [← Finset.card_biUnion hd, hu]
