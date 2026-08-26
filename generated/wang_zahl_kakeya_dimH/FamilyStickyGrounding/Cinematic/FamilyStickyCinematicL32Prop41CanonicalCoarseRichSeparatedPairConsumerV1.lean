import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1

open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

noncomputable section

universe u v w

/-!
# Canonical rich-pair selection for the actual coarse incidence relation

This module removes the identification gap between the abstract `goodPair`
and pair weight in the finite selector and the literal coarse families
`F(R)` supplied by `CoarseRectangleIncidenceData`.

The global lower bound remains an explicit theorem hypothesis.  In
particular, this module does not prove the paper's separated-pair sum lower
bound, ball richness, tangency, or the hypotheses of PYZ Proposition 4.1.
-/

/-- The actual common-coarse-rectangle count, summed over canonically
`10 * ballRadius`-separated ordered pairs. -/
noncomputable def canonicalCoarseRichSeparatedPairCountTotal
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real) : Nat :=
  richSeparatedPairCountTotal N.family
    (canonicalTenRadiusSeparated N ballRadius)
    (D.CoarseGoodPair keep) (D.coarseCrossIncidenceCount keep)

/-- A coarse good pair is exactly a pair of curve indices with retained
genuine incidences over one common literal coarse rectangle. -/
theorem coarseGoodPair_iff_exists_retained_incidence_witnesses
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota) :
    D.CoarseGoodPair keep left right <->
      exists R, R ∈ D.coarseRectangleFamily ∧
        (exists leftFine,
          D.GoodPair left leftFine ∧ keep left leftFine ∧
            D.coarseRectangleAt leftFine = R) ∧
        (exists rightFine,
          D.GoodPair right rightFine ∧ keep right rightFine ∧
            D.coarseRectangleAt rightFine = R) := by
  constructor
  · rintro ⟨R, hR⟩
    have hcommon := (D.mem_commonCoarseRectangleFiber_iff keep).mp hR
    have hleft := (D.mem_coarseCurveIndexFiber_iff keep).mp hcommon.2.1
    have hright := (D.mem_coarseCurveIndexFiber_iff keep).mp hcommon.2.2
    exact ⟨R, hcommon.1, hleft, hright⟩
  · rintro ⟨R, hR, hleft, hright⟩
    refine ⟨R, (D.mem_commonCoarseRectangleFiber_iff keep).mpr ?_⟩
    exact ⟨hR, (D.mem_coarseCurveIndexFiber_iff keep).mpr hleft,
      (D.mem_coarseCurveIndexFiber_iff keep).mpr hright⟩

/-- An explicit positive lower bound for the actual separated-pair sum
selects two canonical centres sharing a retained coarse rectangle.  Besides
the exact denominator-free richness lower bound, the conclusion supplies
`10r` centre separation, `8r` ball cross-separation, and both canonical
non-concentration estimates. -/
theorem exists_canonical_coarse_richSeparated_ballPair
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    {ballRadius : Real}
    (hradiusLower : N.delta <= ballRadius)
    (hradiusUpper : ballRadius <= N.ceiling)
    {lowerBound : Nat} (hlowerBound : 0 < lowerBound)
    (htotal : lowerBound <=
      canonicalCoarseRichSeparatedPairCountTotal N D keep ballRadius) :
    exists left, left ∈ N.family ∧
      exists right, right ∈ N.family ∧
        canonicalTenRadiusSeparated N ballRadius left right ∧
        D.CoarseGoodPair keep left right ∧
        0 < D.coarseCrossIncidenceCount keep left right ∧
        lowerBound <=
          (richSeparatedCenterPairs N.family
              (canonicalTenRadiusSeparated N ballRadius)
              (D.CoarseGoodPair keep)).card *
            D.coarseCrossIncidenceCount keep left right ∧
        (exists R, R ∈ D.coarseRectangleFamily ∧
          (exists leftFine,
            D.GoodPair left leftFine ∧ keep left leftFine ∧
              D.coarseRectangleAt leftFine = R) ∧
          (exists rightFine,
            D.GoodPair right rightFine ∧ keep right rightFine ∧
              D.coarseRectangleAt rightFine = R)) ∧
        FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
          (finiteFamilyMetricBall N.family N.distance ballRadius left)
          (finiteFamilyMetricBall N.family N.distance ballRadius right) ∧
        ((finiteFamilyMetricBall N.family N.distance ballRadius left).card : Real) <=
          (ballRadius / N.criticalScale) ^ N.exponent *
            ((N.criticalBall.card : Nat) : Real) ∧
        ((finiteFamilyMetricBall N.family N.distance ballRadius right).card : Real) <=
          (ballRadius / N.criticalScale) ^ N.exponent *
            ((N.criticalBall.card : Nat) : Real) := by
  have hselected := exists_richSeparated_pair_of_pos_totalCount_lower
    N.family (canonicalTenRadiusSeparated N ballRadius)
      (D.CoarseGoodPair keep) (D.coarseCrossIncidenceCount keep)
      hlowerBound (by
        simpa only [canonicalCoarseRichSeparatedPairCountTotal] using htotal)
  rcases hselected with
    ⟨left, hleft, right, hright, hseparated, hgood, hrich⟩
  have hpositive :=
    (D.coarseGoodPair_iff_crossIncidence_pos keep left right).mp hgood
  have hwitness :=
    (coarseGoodPair_iff_exists_retained_incidence_witnesses
      D keep left right).mp hgood
  have hballs := canonicalMetricBallPair_crossSeparated_and_card_bounds
    N hsymm htriangle hradiusLower hradiusUpper
      left right hleft hright hseparated
  exact ⟨left, hleft, right, hright, hseparated, hgood, hpositive,
    hrich, hwitness, hballs.1, hballs.2.1, hballs.2.2⟩

#print axioms canonicalCoarseRichSeparatedPairCountTotal
#print axioms coarseGoodPair_iff_exists_retained_incidence_witnesses
#print axioms exists_canonical_coarse_richSeparated_ballPair

end

end FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1
