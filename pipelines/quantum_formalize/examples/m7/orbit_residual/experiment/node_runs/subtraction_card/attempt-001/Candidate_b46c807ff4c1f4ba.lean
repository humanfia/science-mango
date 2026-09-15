import FrozenTarget_b46c807ff4c1f4ba
theorem M7.OrbitResidual.subtraction_card : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N inst C bases hsep
    have hsum : (∑ c ∈ bases, (M7.ActualOrbit.distinctCount c (fun y => y ∈ C) : ℤ)) = ((C ∩ M7.OrbitResidual.covered bases).card : ℤ) := by
      exact_mod_cast (M7.OrbitResidual.sum_intersections N C bases hsep)
    have hcard : ((C \ M7.OrbitResidual.covered bases).card : ℤ) + ((C ∩ M7.OrbitResidual.covered bases).card : ℤ) = (C.card : ℤ) := by
      exact_mod_cast (Finset.card_sdiff_add_card_inter C (M7.OrbitResidual.covered bases))
    unfold M7.OrbitResidual.subtraction M7.OrbitResidual.remaining
    rw [hsum]
    omega
