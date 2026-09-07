import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighFirstHitTubeOccurrenceWeightV1

open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open Family8Family7NativeHighWeightedCriticalBallV1

noncomputable section

universe u v

/-!
# Convert first-hit fine-label mass to honest tube-occurrence weight

Each first-hit `Y₂` label has an exact planar mass and a nonempty finite fibre
of genuine active tube indices.  Divide the label mass equally over that
fibre, then sum over labels incident to a fixed tube.  Finite Fubini and exact
cardinality cancellation show that the total tube weight is exactly the
original first-hit mass.  Every positive-weight tube lies in the same
canonical norm family `N.family`.

This is an actual producer for the weighted critical-ball selector: it uses
only literal first-hit masses and active incidence fibres, never a requested
mass conclusion.
-/

/-- Equal-share occurrence weight assigned to one original tube index. -/
noncomputable def actualGPrimeE2FirstHitTubeOccurrenceWeight
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (i : iota) : ENNReal :=
  ∑ r ∈ D.fineLabels,
    if i ∈ actualGPrimeRetainedFineActiveFiber N D (fun _ _ => True) r then
      actualGPrimeE2FirstHitLabelWeight D label r /
        ((actualGPrimeRetainedFineActiveFiber N D
          (fun _ _ => True) r).card : ENNReal)
    else 0

/-- Positive occurrence weight is supported on the literal canonical norm
family, directly from the retained-fibre intersection definition. -/
theorem actualGPrimeE2FirstHitTubeOccurrenceWeight_support
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) {i : iota}
    (hi : actualGPrimeE2FirstHitTubeOccurrenceWeight N D label i ≠ 0) :
    i ∈ N.family := by
  classical
  by_contra hiFamily
  apply hi
  unfold actualGPrimeE2FirstHitTubeOccurrenceWeight
  apply Finset.sum_eq_zero
  intro r hr
  simp only [actualGPrimeRetainedFineActiveFiber, Finset.mem_inter,
    hiFamily, and_false, if_false]

private theorem sum_equalShare_over_family
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (r : fineLabel)
    (hfiber : (actualGPrimeRetainedFineActiveFiber N D
      (fun _ _ => True) r).Nonempty) :
    (∑ i ∈ N.family,
      if i ∈ actualGPrimeRetainedFineActiveFiber N D
          (fun _ _ => True) r then
        actualGPrimeE2FirstHitLabelWeight D label r /
          ((actualGPrimeRetainedFineActiveFiber N D
            (fun _ _ => True) r).card : ENNReal)
      else 0) = actualGPrimeE2FirstHitLabelWeight D label r := by
  classical
  let fiber := actualGPrimeRetainedFineActiveFiber N D
    (fun _ _ => True) r
  have hfiberSubset : fiber ⊆ N.family := by
    intro i hi
    exact (Finset.mem_inter.mp hi).2
  have hfilter : N.family.filter (fun i => i ∈ fiber) = fiber := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi => hi.2
    · exact fun hi => ⟨hfiberSubset hi, hi⟩
  calc
    (∑ i ∈ N.family, if i ∈ fiber then
        actualGPrimeE2FirstHitLabelWeight D label r /
          (fiber.card : ENNReal) else 0) =
      ∑ i ∈ N.family.filter (fun i => i ∈ fiber),
        actualGPrimeE2FirstHitLabelWeight D label r /
          (fiber.card : ENNReal) := by
        rw [Finset.sum_filter]
    _ = ∑ i ∈ fiber,
        actualGPrimeE2FirstHitLabelWeight D label r /
          (fiber.card : ENNReal) := by rw [hfilter]
    _ = (fiber.card : ENNReal) *
        (actualGPrimeE2FirstHitLabelWeight D label r /
          (fiber.card : ENNReal)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = actualGPrimeE2FirstHitLabelWeight D label r := by
      rw [mul_comm]
      exact ENNReal.div_mul_cancel
        (by exact_mod_cast (Finset.card_ne_zero.mpr hfiber))
        (ENNReal.natCast_ne_top _)

/-- Exact finite Fubini: normalized tube occurrences retain the whole
first-hit fine-label mass, with no fibre-cardinality loss. -/
theorem sum_actualGPrimeE2FirstHitTubeOccurrenceWeight_eq_labelWeight
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int)
    (hfiber : ∀ r, r ∈ D.fineLabels →
      (actualGPrimeRetainedFineActiveFiber N D
        (fun _ _ => True) r).Nonempty) :
    (∑ i ∈ N.family,
      actualGPrimeE2FirstHitTubeOccurrenceWeight N D label i) =
      ∑ r ∈ D.fineLabels,
        actualGPrimeE2FirstHitLabelWeight D label r := by
  classical
  unfold actualGPrimeE2FirstHitTubeOccurrenceWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact sum_equalShare_over_family N D label r (hfiber r hr)

/-- Combining the exact first-hit package with occurrence Fubini identifies
the total tube weight with the literal projected E2 cell mass. -/
theorem sum_actualGPrimeE2FirstHitTubeOccurrenceWeight_eq_E2Mass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) (ballRadius : Real)
    (Q : ActualGPrimeE2FirstHitWeightedSampledOutcome
      N D label ballRadius)
    (hfiber : ∀ r, r ∈ D.fineLabels →
      (actualGPrimeRetainedFineActiveFiber N D
        (fun _ _ => True) r).Nonempty) :
    (∑ i ∈ N.family,
      actualGPrimeE2FirstHitTubeOccurrenceWeight N D label i) =
      volume (projectedPositiveMultiplicityDyadicCell D.shading label) := by
  rw [sum_actualGPrimeE2FirstHitTubeOccurrenceWeight_eq_labelWeight
    N D label hfiber]
  exact Q.firstHit_mass_eq

/-- The actual tube-occurrence weight feeds the mass-weighted canonical
selector on exactly the same norm family and metric. -/
noncomputable def actualGPrimeE2FirstHitWeightedNormData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) : WeightedCanonicalNormBallData iota where
  family := N.family
  distance := N.distance
  weight := actualGPrimeE2FirstHitTubeOccurrenceWeight N D label
  delta := N.delta
  ceiling := N.ceiling
  exponent := N.exponent
  family_nonempty := N.family_nonempty
  self_le_delta := N.self_le_delta
  delta_pos := N.delta_pos
  delta_le_ceiling := N.delta_le_ceiling
  exponent_nonneg := N.exponent_nonneg

#print axioms actualGPrimeE2FirstHitTubeOccurrenceWeight
#print axioms actualGPrimeE2FirstHitTubeOccurrenceWeight_support
#print axioms sum_actualGPrimeE2FirstHitTubeOccurrenceWeight_eq_labelWeight
#print axioms sum_actualGPrimeE2FirstHitTubeOccurrenceWeight_eq_E2Mass
#print axioms actualGPrimeE2FirstHitWeightedNormData

end

end Family8Family7NativeHighFirstHitTubeOccurrenceWeightV1
