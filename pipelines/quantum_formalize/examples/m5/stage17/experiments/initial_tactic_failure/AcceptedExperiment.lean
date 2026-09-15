import M5FiniteExclusion

theorem M5.FiniteExclusion.alternating_subsets : ∀ S : Finset M5.BinaryPolynomial, (∑ H ∈ S.powerset, (-1 : ℤ)^H.card) = if S = ∅ then 1 else 0 := by
  classical
  change ∀ S : Finset M5.BinaryPolynomial, (∑ H ∈ S.powerset, (-1 : ℤ) ^ H.card) = if S = ∅ then 1 else 0
  intro S
  first
    | exact Finset.sum_powerset_neg_one_pow_card
    | exact Nat.sum_powerset_neg_one_pow_card

theorem M5.FiniteExclusion.filtered_powerset : ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), S.powerset.filter (fun H => ∀ p ∈ H, bad p = true) = (S.filter (fun p => bad p = true)).powerset := by
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
#print axioms M5.FiniteExclusion.alternating_subsets
#print axioms M5.FiniteExclusion.filtered_powerset
