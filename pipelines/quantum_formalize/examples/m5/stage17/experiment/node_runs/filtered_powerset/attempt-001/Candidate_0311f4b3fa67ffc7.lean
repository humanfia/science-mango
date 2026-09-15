import FrozenTarget_0311f4b3fa67ffc7
theorem M5.FiniteExclusion.filtered_powerset : QuantumHarnessFrozenTarget := by
  change ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), S.powerset.filter (fun H => ∀ p ∈ H, bad p = true) = (S.filter (fun p => bad p = true)).powerset
  intro S bad
  classical
  apply Finset.ext
  intro H
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hHS, hbad⟩
    intro p hp
    exact Finset.mem_filter.mpr ⟨hHS hp, hbad p hp⟩
  · intro hH
    constructor
    · intro p hp
      exact (Finset.mem_filter.mp (hH hp)).1
    · intro p hp
      exact (Finset.mem_filter.mp (hH hp)).2
