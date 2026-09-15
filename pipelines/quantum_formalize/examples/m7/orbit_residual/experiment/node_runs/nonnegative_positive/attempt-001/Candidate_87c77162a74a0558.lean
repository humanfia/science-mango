import FrozenTarget_87c77162a74a0558
theorem M7.OrbitResidual.nonnegative_positive : QuantumHarnessFrozenTarget := by
  classical
  intro N inst C bases hsep
  rw [M7.OrbitResidual.subtraction_card N C bases hsep]
  constructor
  · positivity
  · constructor
    · intro h
      have hcard : 0 < (M7.OrbitResidual.remaining C bases).card := by omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard
      have hy' : y ∈ C ∧ y ∉ M7.OrbitResidual.covered bases := by
        simpa [M7.OrbitResidual.remaining] using hy
      exact ⟨y, hy'.1, hy'.2⟩
    · rintro ⟨y, hyC, hy⟩
      have hmem : y ∈ M7.OrbitResidual.remaining C bases := by
        simpa [M7.OrbitResidual.remaining] using And.intro hyC hy
      have hcard := Finset.card_pos.mpr ⟨y, hmem⟩
      omega
