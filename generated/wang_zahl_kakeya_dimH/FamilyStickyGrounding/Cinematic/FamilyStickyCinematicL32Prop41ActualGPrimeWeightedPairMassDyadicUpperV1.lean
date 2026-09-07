import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
import FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualGPrimeWeightedPairMassDyadicUpperV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u v

/-!
# Dyadic upper bound for the actual weighted separated-pair mass

The genuine separated-pair carrier at one fine label is a filtered subset of
the square of its retained active fibre.  On an actual E2 dyadic cell that
fibre has cardinality at most `pyzE2DegreeUpper label`.  Consequently the
weighted pair mass is at most the square of that degree times the literal
first-hit label mass.  No ambient-cardinality or pair-packing callback is
used.
-/

/-- A separated-pair fibre is no larger than the square of its retained
active fibre. -/
theorem actualGPrimeFineSeparatedPairsAt_card_le_active_sq
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (r : fineLabel) :
    (actualGPrimeFineSeparatedPairsAt N D keep ballRadius r).card <=
      (actualGPrimeRetainedFineActiveFiber N D keep r).card *
        (actualGPrimeRetainedFineActiveFiber N D keep r).card := by
  have hpartition := actualGPrimeFineSeparated_card_add_near_card
    N D keep ballRadius r
  omega

/-- On the literal E2 dyadic cell, the retained fibre with trivial keep
predicate has the canonical integer degree upper bound. -/
theorem actualGPrimeRetainedFineActiveFiber_true_card_le_degreeUpper
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (r : fineLabel) (hr : r ∈ D.fineLabels)
    (hcell : D.pointAt r ∈
      projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hsubset : D.shading.activeAtPoint (D.pointAt r) ⊆ N.family) :
    (actualGPrimeRetainedFineActiveFiber
      N D (fun _ _ => True) r).card <= pyzE2DegreeUpper label := by
  rw [actualGPrimeRetainedFineActiveFiber_true_eq_activeAtPoint
    N D r hr hsubset]
  exact active_card_le_pyzE2DegreeUpper_of_mem_cell
    D.shading label (D.pointAt r) hcell hactive

/-- The full weighted separated-pair mass on an actual dyadic E2 family is
bounded by `degreeUpper²` times the same literal label-weight sum. -/
theorem actualGPrimeWeightedFineSeparatedPairMass_le_degreeUpper_sq_mul_weightSum
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (ballRadius : Real) (labelWeight : fineLabel -> ENNReal)
    (hcell : forall r, r ∈ D.fineLabels -> D.pointAt r ∈
      projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hsubset : forall r, r ∈ D.fineLabels ->
      D.shading.activeAtPoint (D.pointAt r) ⊆ N.family) :
    actualGPrimeWeightedFineSeparatedPairMass N D (fun _ _ => True)
        ballRadius labelWeight <=
      (((pyzE2DegreeUpper label * pyzE2DegreeUpper label : Nat) :
          ENNReal) *
        ∑ r ∈ D.fineLabels, labelWeight r) := by
  unfold actualGPrimeWeightedFineSeparatedPairMass
  calc
    (∑ r ∈ D.fineLabels,
        labelWeight r *
          ((actualGPrimeFineSeparatedPairsAt N D (fun _ _ => True)
            ballRadius r).card : ENNReal)) <=
      ∑ r ∈ D.fineLabels,
        labelWeight r *
          ((pyzE2DegreeUpper label * pyzE2DegreeUpper label : Nat) :
            ENNReal) := by
      apply Finset.sum_le_sum
      intro r hr
      gcongr
      exact_mod_cast
        (actualGPrimeFineSeparatedPairsAt_card_le_active_sq
          N D (fun _ _ => True) ballRadius r).trans
            (Nat.mul_le_mul
              (actualGPrimeRetainedFineActiveFiber_true_card_le_degreeUpper
                N D label r hr (hcell r hr) (hactive r hr) (hsubset r hr))
              (actualGPrimeRetainedFineActiveFiber_true_card_le_degreeUpper
                N D label r hr (hcell r hr) (hactive r hr) (hsubset r hr)))
    _ = (((pyzE2DegreeUpper label * pyzE2DegreeUpper label : Nat) :
            ENNReal) *
          ∑ r ∈ D.fineLabels, labelWeight r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

#print axioms actualGPrimeFineSeparatedPairsAt_card_le_active_sq
#print axioms actualGPrimeRetainedFineActiveFiber_true_card_le_degreeUpper
#print axioms actualGPrimeWeightedFineSeparatedPairMass_le_degreeUpper_sq_mul_weightSum

end

end FamilyStickyCinematicL32Prop41ActualGPrimeWeightedPairMassDyadicUpperV1
