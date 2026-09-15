import FrozenTarget_6a24a7ff9ca44ce9
theorem M7.OrbitResidual.sum_intersections : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N inst C bases hsep
  change M7.OrbitResidual.Separated bases at hsep
  have hcount (c : M7.Action.Recipe N) :
      M7.ActualOrbit.distinctCount c (fun y => y ∈ C) =
        ((M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)).card := by
    simp only [M7.ActualOrbit.distinctCount, M7.ActualOrbit.orbit,
      Finset.filter_image]
  calc
    _ = ∑ c ∈ bases, ((M7.ActualOrbit.orbit c).filter (fun y => y ∈ C)).card := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hcount c
    _ = (bases.biUnion (fun c => (M7.ActualOrbit.orbit c).filter (fun y => y ∈ C))).card := by
      symm
      apply Finset.card_biUnion
      intro c hc d hd hcd
      exact (hsep c hc d hd hcd).mono
        (Finset.filter_subset _)
        (Finset.filter_subset _)
    _ = (C ∩ M7.OrbitResidual.covered bases).card := by
      congr 1
      ext y
      simp only [M7.OrbitResidual.covered, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_inter]
      aesop
