import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLeaderWeightedCSV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLeaderReciprocalFourV1

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedCoreV1

open FamilyStickyCinematicL32Prop41MarcusTardosLemmaTwoSumAlgebraV1
open FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1
open FamilyStickyCinematicL32Prop41MarcusTardosLeaderWeightedCSV1
open FamilyStickyCinematicL32Prop41MarcusTardosLeaderReciprocalFourV1

/-! # Faithful weighted leader aggregation in Marcus--Tardos Lemma 5 -/

theorem leaderWeightedSquare_le_totalWeightedRegularSquare
    {level : Type*} [Fintype level] [DecidableEq level]
    {pair : level → Type*} [∀ l, Fintype (pair l)]
    [∀ l, DecidableEq (pair l)]
    (leaders : Finset (Sigma pair))
    (weight : level → Real) (mass : ∀ l, pair l → Real)
    (singular : ∀ l, pair l → Prop)
    (hweight : ∀ l, 0 < weight l)
    (hregular : ∀ x ∈ leaders, ¬singular x.1 x.2) :
    leaderWeightedSquare leaders weight mass ≤
      totalWeightedRegularSquare weight mass singular := by
  classical
  calc
    leaderWeightedSquare leaders weight mass =
        ∑ x ∈ leaders, if singular x.1 x.2 then 0
          else weight x.1 * (mass x.1 x.2) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hregular x hx]
    _ ≤ ∑ x : Sigma pair, if singular x.1 x.2 then 0
          else weight x.1 * (mass x.1 x.2) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ leaders) (fun x hx hnot => by
          by_cases hs : singular x.1 x.2
          · simp [hs]
          · simp only [hs, ↓reduceIte]
            exact mul_nonneg (hweight x.1).le (sq_nonneg _))
    _ = totalWeightedRegularSquare weight mass singular := by
      rw [Fintype.sum_sigma]
      unfold totalWeightedRegularSquare regularSquareMass
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hs : singular l p <;> simp [hs]

theorem totalWeightedQ_add_regularSquare_le
    {level : Type*} [Fintype level] [DecidableEq level]
    {pair : level → Type*} [∀ l, Fintype (pair l)]
    [∀ l, DecidableEq (pair l)]
    (weight : level → Real) (q mass : ∀ l, pair l → Real)
    (singular : ∀ l, pair l → Prop) (totalMass : Real)
    (hweight : ∀ l, 0 < weight l)
    (hlevel : ∀ l,
      (∑ p, q l p) + regularSquareMass (singular l) (mass l) ≤
        totalMass) :
    totalWeightedQ weight q +
      totalWeightedRegularSquare weight mass singular ≤
      totalMass * ∑ l, weight l := by
  classical
  unfold totalWeightedQ totalWeightedRegularSquare
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ l, weight l *
          ((∑ p, q l p) + regularSquareMass (singular l) (mass l)) := by
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ ≤ ∑ l, weight l * totalMass := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_left (hlevel l) (hweight l).le
    _ = totalMass * ∑ l, weight l := by
      rw [← Finset.sum_mul]
      ring

theorem lemmaFive_denominatorFree
    {level : Type*} [Fintype level] [DecidableEq level]
    {pair : level → Type*} [∀ l, Fintype (pair l)]
    [∀ l, DecidableEq (pair l)]
    (weight : level → Real) (q mass : ∀ l, pair l → Real)
    (singular : ∀ l, pair l → Prop) (totalMass : Real)
    (leaders : Finset (Sigma pair))
    (hweight : ∀ l, 0 < weight l)
    (hlevel : ∀ l,
      (∑ p, q l p) + regularSquareMass (singular l) (mass l) ≤
        totalMass)
    (hleaderRegular : ∀ x ∈ leaders, ¬singular x.1 x.2)
    (hleaderFour : ∀ l,
      (leaders.filter fun x => x.1 = l).card ≤ 4)
    (hleaderMass : leaderMass leaders mass = totalMass) :
    totalWeightedQ weight q + leaderWeightedSquare leaders weight mass ≤
        totalMass * ∑ l, weight l ∧
      totalMass ^ 2 ≤
        4 * (∑ l, (weight l)⁻¹) *
          leaderWeightedSquare leaders weight mass := by
  constructor
  · calc
      totalWeightedQ weight q + leaderWeightedSquare leaders weight mass ≤
          totalWeightedQ weight q +
            totalWeightedRegularSquare weight mass singular := by
        exact add_le_add_right
          (leaderWeightedSquare_le_totalWeightedRegularSquare
            leaders weight mass singular hweight hleaderRegular) _
      _ ≤ totalMass * ∑ l, weight l :=
        totalWeightedQ_add_regularSquare_le
          weight q mass singular totalMass hweight hlevel
  · have hreciprocal := sum_leader_reciprocal_le_four_mul_sum
      leaders (fun x => x.1) weight hweight hleaderFour
    have hcs := sum_mass_sq_le_four_mul_weightedSquare_mul
      leaders (fun x => weight x.1) (fun x => mass x.1 x.2)
      (∑ l, (weight l)⁻¹)
      (fun x hx => hweight x.1) hreciprocal
    rw [← hleaderMass]
    simpa [leaderMass, leaderWeightedSquare] using hcs

#print axioms leaderWeightedSquare_le_totalWeightedRegularSquare
#print axioms totalWeightedQ_add_regularSquare_le
#print axioms lemmaFive_denominatorFree

end FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedCoreV1
