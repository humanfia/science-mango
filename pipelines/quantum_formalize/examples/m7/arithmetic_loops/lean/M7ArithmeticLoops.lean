import M7ResiduePrefixAccepted

namespace M7.ArithmeticLoops
open scoped BigOperators
noncomputable def factorCount (N : ℕ) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N)).toFinset.card
noncomputable def divisorCount (N : ℕ) : ℕ := N.divisors.card
/-- Actual character-loop repetitions in the two nSelected calls of completionC.
    ValidSector makes every selected exclusion polynomial monic, so neither call is skipped. -/
noncomputable def characterVisits (N w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B : Finset ℕ) : ℕ := by
  classical
  exact if A.card ≤ w ∧ B.card ≤ w then
    ∑ F ∈ E, ∑ _d ∈ (M5.Connectivity.supportGcd N A B).divisors,
      ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        2 * Fintype.card (M5.Character.BinaryVector (F * (∏ p ∈ S, p)).natDegree)
    else 0
end M7.ArithmeticLoops
