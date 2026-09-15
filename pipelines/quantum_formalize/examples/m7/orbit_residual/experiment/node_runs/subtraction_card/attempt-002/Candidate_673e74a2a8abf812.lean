import FrozenTarget_673e74a2a8abf812
theorem M7.OrbitResidual.subtraction_card : QuantumHarnessFrozenTarget := by
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
