import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set
open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32FiniteValueFibresV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1

noncomputable section

universe u v w

/-!
# Package-free grid-right-C/local-cover refinement

The finite carrier, fine-label map, raw right endpoint, and grid-normalised
right tube are arbitrary.  We partition by the literal pair

`(tubeGraphC (rightTube a), source-cover code a)`.

Thus this module does not depend on an actual shifted-grid package.  Its only
grid-specific geometric input is the explicit bound between the retained raw
right endpoint and `rightTube`.
-/

abbrev ActualY1GridRightCLocalCoverSelectedItem
    {item : Type u} [DecidableEq item] (selected : Finset item) :=
  ActualY1RightCLocalCoverSelectedItem selected

def actualY1GridRightCLocalCoverSourceTube
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) :
    ActualY1GridRightCLocalCoverSelectedItem selected -> Tube radius :=
  actualY1RightCLocalCoverSourceTube selected labelAt pointAt tubeAt

noncomputable def actualY1GridRightCLocalCoverCode
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    ActualY1GridRightCLocalCoverSelectedItem selected -> Tube radius :=
  actualY1RightCLocalCoverCode selected labelAt pointAt tubeAt ballRadius

noncomputable def actualY1GridRightCLocalCoverValue
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    ActualY1GridRightCLocalCoverSelectedItem selected -> Real × Tube radius :=
  fun a =>
    (tubeGraphC (rightTube a.1),
      actualY1GridRightCLocalCoverCode selected labelAt pointAt tubeAt
        ballRadius a)

noncomputable def actualY1GridRightCLocalCoverFiber
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius) :
    Finset (ActualY1GridRightCLocalCoverSelectedItem selected) :=
  finiteValueFiber Finset.univ
    (actualY1GridRightCLocalCoverValue selected labelAt rightTube pointAt
      tubeAt ballRadius) value

noncomputable def actualY1GridRightCLocalCoverValues
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    Finset (Real × Tube radius) :=
  finiteOccupiedValues Finset.univ
    (actualY1GridRightCLocalCoverValue selected labelAt rightTube pointAt
      tubeAt ballRadius)

noncomputable def actualY1GridRightCLocalCoverUnderlyingFiber
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius) : Finset item :=
  (actualY1GridRightCLocalCoverFiber selected labelAt rightTube pointAt
    tubeAt ballRadius value).image Subtype.val

def actualY1GridRightCLocalCoverExactLocalRectangle
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u}
    {fineLabel : Type v} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (labelAt : item -> fineLabel) (localDelta localScale : Real) :
    item -> C2GraphRectangle :=
  actualY1RightCLocalCoverExactLocalRectangle D labelAt localDelta localScale

theorem actualY1GridRightCLocalCoverFiber_nonempty
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius)
    (hvalue : value ∈ actualY1GridRightCLocalCoverValues selected labelAt
      rightTube pointAt tubeAt ballRadius) :
    (actualY1GridRightCLocalCoverFiber selected labelAt rightTube pointAt
      tubeAt ballRadius value).Nonempty :=
  finiteValueFiber_nonempty_of_mem Finset.univ
    (actualY1GridRightCLocalCoverValue selected labelAt rightTube pointAt
      tubeAt ballRadius) hvalue

theorem actualY1GridRightCLocalCoverUnderlyingFiber_subset
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius) :
    actualY1GridRightCLocalCoverUnderlyingFiber selected labelAt rightTube
      pointAt tubeAt ballRadius value ⊆ selected := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨b, _hb, rfl⟩
  exact b.2

theorem actualY1GridRightCLocalCoverUnderlyingFiber_nonempty
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius)
    (hvalue : value ∈ actualY1GridRightCLocalCoverValues selected labelAt
      rightTube pointAt tubeAt ballRadius) :
    (actualY1GridRightCLocalCoverUnderlyingFiber selected labelAt rightTube
      pointAt tubeAt ballRadius value).Nonempty := by
  rcases actualY1GridRightCLocalCoverFiber_nonempty selected labelAt rightTube
    pointAt tubeAt ballRadius value hvalue with ⟨a, ha⟩
  exact ⟨a.1, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩

theorem actualY1GridRightCLocalCoverUnderlyingFiber_card
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius) :
    (actualY1GridRightCLocalCoverUnderlyingFiber selected labelAt rightTube
      pointAt tubeAt ballRadius value).card =
      (actualY1GridRightCLocalCoverFiber selected labelAt rightTube pointAt
        tubeAt ballRadius value).card := by
  unfold actualY1GridRightCLocalCoverUnderlyingFiber
  exact Finset.card_image_of_injective _ Subtype.val_injective

theorem pairwiseDisjoint_actualY1GridRightCLocalCoverFiber
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    Set.PairwiseDisjoint
      (actualY1GridRightCLocalCoverValues selected labelAt rightTube pointAt
        tubeAt ballRadius : Set (Real × Tube radius))
      (actualY1GridRightCLocalCoverFiber selected labelAt rightTube pointAt
        tubeAt ballRadius) := by
  exact pairwiseDisjoint_finiteValueFiber Finset.univ
    (actualY1GridRightCLocalCoverValue selected labelAt rightTube pointAt
      tubeAt ballRadius)

theorem biUnion_actualY1GridRightCLocalCoverFiber_eq_univ
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    (actualY1GridRightCLocalCoverValues selected labelAt rightTube pointAt
      tubeAt ballRadius).biUnion
        (actualY1GridRightCLocalCoverFiber selected labelAt rightTube pointAt
          tubeAt ballRadius) = Finset.univ := by
  exact biUnion_finiteValueFiber_eq Finset.univ
    (actualY1GridRightCLocalCoverValue selected labelAt rightTube pointAt
      tubeAt ballRadius)

theorem actualY1GridRightCLocalCover_selected_card_eq_sum_fiber_card
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    selected.card =
      ∑ value ∈ actualY1GridRightCLocalCoverValues selected labelAt rightTube
        pointAt tubeAt ballRadius,
        (actualY1GridRightCLocalCoverFiber selected labelAt rightTube pointAt
          tubeAt ballRadius value).card := by
  rw [← Fintype.card_coe selected]
  simpa only [Finset.card_univ, actualY1GridRightCLocalCoverValues,
    actualY1GridRightCLocalCoverFiber] using
      card_eq_sum_finiteValueFiber_card
        (Finset.univ : Finset
          (ActualY1GridRightCLocalCoverSelectedItem selected))
        (actualY1GridRightCLocalCoverValue selected labelAt rightTube pointAt
          tubeAt ballRadius)

theorem actualY1GridRightCLocalCoverFiber_rightGraphC
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius)
    (a : ActualY1GridRightCLocalCoverSelectedItem selected)
    (ha : a ∈ actualY1GridRightCLocalCoverFiber selected labelAt rightTube
      pointAt tubeAt ballRadius (c, coverCenter)) :
    tubeGraphC (rightTube a.1) = c := by
  have haValue := (mem_finiteValueFiber_iff Finset.univ
    (actualY1GridRightCLocalCoverValue selected labelAt rightTube pointAt
      tubeAt ballRadius) (c, coverCenter) a).mp ha |>.2
  simpa only [actualY1GridRightCLocalCoverValue] using
    congrArg Prod.fst haValue

theorem actualY1GridRightCLocalCoverUnderlyingFiber_rightGraphC
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius) :
    forall a, a ∈ actualY1GridRightCLocalCoverUnderlyingFiber selected labelAt
      rightTube pointAt tubeAt ballRadius (c, coverCenter) ->
      tubeGraphC (rightTube a) = c := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
  exact actualY1GridRightCLocalCoverFiber_rightGraphC selected labelAt
    rightTube pointAt tubeAt ballRadius c coverCenter b hb

theorem actualY1GridRightCLocalCoverUnderlyingFiber_leftGraphC_of_pair
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube leftTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius)
    (hpair : forall a, a ∈ selected ->
      tubeGraphC (leftTube a) = tubeGraphC (rightTube a)) :
    forall a, a ∈ actualY1GridRightCLocalCoverUnderlyingFiber selected labelAt
      rightTube pointAt tubeAt ballRadius (c, coverCenter) ->
      tubeGraphC (leftTube a) = c := by
  intro a ha
  exact (hpair a
    (actualY1GridRightCLocalCoverUnderlyingFiber_subset selected labelAt
      rightTube pointAt tubeAt ballRadius (c, coverCenter) ha)).trans
        (actualY1GridRightCLocalCoverUnderlyingFiber_rightGraphC selected
          labelAt rightTube pointAt tubeAt ballRadius c coverCenter a ha)

theorem actualY1GridRightCLocalCoverFiber_coverCode_eq
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius)
    (a : ActualY1GridRightCLocalCoverSelectedItem selected)
    (ha : a ∈ actualY1GridRightCLocalCoverFiber selected labelAt rightTube
      pointAt tubeAt ballRadius (c, coverCenter)) :
    actualY1GridRightCLocalCoverCode selected labelAt pointAt tubeAt
      ballRadius a = coverCenter := by
  have haValue := (mem_finiteValueFiber_iff Finset.univ
    (actualY1GridRightCLocalCoverValue selected labelAt rightTube pointAt
      tubeAt ballRadius) (c, coverCenter) a).mp ha |>.2
  simpa only [actualY1GridRightCLocalCoverValue] using
    congrArg Prod.snd haValue

theorem actualY1GridRightCLocalCoverUnderlyingFiber_coverCode_eq
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius) (a : item)
    (ha : a ∈ actualY1GridRightCLocalCoverUnderlyingFiber selected labelAt
      rightTube pointAt tubeAt ballRadius (c, coverCenter))
    (hselected : a ∈ selected) :
    actualY1GridRightCLocalCoverCode selected labelAt pointAt tubeAt
      ballRadius ⟨a, hselected⟩ = coverCenter := by
  rcases Finset.mem_image.mp ha with ⟨b, hb, hba⟩
  subst a
  simpa using actualY1GridRightCLocalCoverFiber_coverCode_eq selected labelAt
    rightTube pointAt tubeAt ballRadius c coverCenter b hb

/-! ## C-normalized numerical budget -/

/-- The C-normalized smallness has enough room for both the active-bucket
`radius / 2` error and the grid-normalisation `radius` error. -/
theorem three_halves_radius_le_eight_ballRadius_of_cNormalizedThreeShiftSmall
    {radius : NNReal} {globalDelta tGlobal ballRadius A B : Real}
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (B - A))
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius)) :
    3 * (radius : Real) / 2 <= 8 * ballRadius := by
  have scales :=
    actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall
      sharp hsmall
  have hfactor := q_le_prop41TangencyScaleFactor_of_one_le scales.traceQ_one
  have hfactorOne : 1 <=
      prop41TangencyScaleFactor
        (actualY1PaperFineCNormalizedChoiceTraceQ
          (radius : Real) globalDelta tGlobal (4 * ballRadius)) :=
    scales.traceQ_one.trans hfactor
  have hsum : 10 <=
      10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            (radius : Real) globalDelta tGlobal (4 * ballRadius)) +
        actualY1PaperFineCNormalizedChoiceLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius) := by
    nlinarith [scales.lambda_pos]
  have hlarge : 1 <=
      46080 *
        (10 * prop41TangencyScaleFactor
            (actualY1PaperFineCNormalizedChoiceTraceQ
              (radius : Real) globalDelta tGlobal (4 * ballRadius)) +
          actualY1PaperFineCNormalizedChoiceLambda
            (radius : Real) globalDelta tGlobal (4 * ballRadius)) := by
    nlinarith
  have hradius : 0 <= (radius : Real) := NNReal.coe_nonneg radius
  have hsmall' :
      46080 *
          (10 * prop41TangencyScaleFactor
              (actualY1PaperFineCNormalizedChoiceTraceQ
                (radius : Real) globalDelta tGlobal (4 * ballRadius)) +
            actualY1PaperFineCNormalizedChoiceLambda
              (radius : Real) globalDelta tGlobal (4 * ballRadius)) *
        (radius : Real) < 4 * ballRadius := by
    simpa only [ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness] using
      hsmall
  have hradiusLt : (radius : Real) < 4 * ballRadius := by
    nlinarith
  nlinarith

/-! ## Actual Y1 local geometry -/

/-- A retained raw right endpoint gives the active `radius / 2` C-error.  An
arbitrary fixed grid transform gives one further `radius`; their triangle
sum fits the same twelve-`ballRadius` local C2 ball. -/
theorem actualY1GridRightCLocalCoverFiber_hballLocal
    {radius : NNReal} {iota : Type w} [DecidableEq iota]
    {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hfDeriv hf1Deriv
      tGlobal globalDelta)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (fineDelta fineScale coarseDelta coarseScale : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
    (keep : iota -> fineLabel -> Prop)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (rightTube : item -> Tube radius)
    (hrightRetained : forall a, a ∈ selected ->
      (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep)
    (hgridCError : forall a, a ∈ selected ->
      |tubeGraphC (fine.tubes (rightIndex a)) - tubeGraphC (rightTube a)| <=
        (radius : Real))
    (localDelta ballRadius : Real)
    (hballRadius : 0 < ballRadius)
    (hcBudget : 3 * (radius : Real) / 2 <= 8 * ballRadius)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (c : Real) (coverCenter : Tube radius) :
    forall a,
      a ∈ actualY1GridRightCLocalCoverFiber selected labelAt rightTube
        pointAt tubeAt ballRadius (c, coverCenter) ->
      InPointwiseC2BallOn (Icc outerA outerB)
        (globalCenterFixedCommonCReference coverCenter c f f1 f2
          hfDeriv hf1Deriv outerA outerB hOuter)
        (actualY1GridRightCLocalCoverExactLocalRectangle D labelAt localDelta
          (4 * ballRadius) a.1)
        (3 * (4 * ballRadius)) := by
  subst D
  intro a ha
  let r := labelAt a.1
  let i := rightIndex a.1
  have hretained := hrightRetained a.1 a.2
  have hactiveData := y1FineCoarseRectangleData_retainedPair_active fine Y1
    fineLabels pointAt tubeAt f f1 f2 hfDeriv hf1Deriv fineDelta fineScale
      coarseDelta coarseScale keep i r hretained
  have hqE : pointAt r ∈ E := hpointE r hactiveData.1
  have hcEndpoint : tubeGraphC (rightTube a.1) = c := by
    exact actualY1GridRightCLocalCoverFiber_rightGraphC selected labelAt
      rightTube pointAt tubeAt ballRadius c coverCenter a ha
  have hcRaw := facts.hactiveCBucket (pointAt r) hqE i hactiveData.2.1
  have hgrid := hgridCError a.1 a.2
  have hcError : |tubeGraphC (tubeAt (pointAt r)) - c| <=
      3 * (radius : Real) / 2 := by
    rw [← hcEndpoint]
    calc
      |tubeGraphC (tubeAt (pointAt r)) - tubeGraphC (rightTube a.1)| <=
          |tubeGraphC (tubeAt (pointAt r)) - tubeGraphC (fine.tubes i)| +
            |tubeGraphC (fine.tubes i) - tubeGraphC (rightTube a.1)| :=
        abs_sub_le _ _ _
      _ <= (radius : Real) / 2 + (radius : Real) :=
        add_le_add (by simpa only [abs_sub_comm] using hcRaw) hgrid
      _ = 3 * (radius : Real) / 2 := by ring
  have hcoverEq :
      actualY1GridRightCLocalCoverCode selected labelAt pointAt tubeAt
        ballRadius a = coverCenter :=
    actualY1GridRightCLocalCoverFiber_coverCode_eq selected labelAt rightTube
      pointAt tubeAt ballRadius c coverCenter a ha
  have hcoverDistance :
      tubePairCoefficientDistance (tubeAt (pointAt r)) coverCenter <
        ballRadius := by
    have hcover := sourceTube_distance_coverCode_lt
      (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt tubeAt)
      ballRadius hballRadius a
    have hcover' :
        tubePairCoefficientDistance (tubeAt (pointAt r))
          (actualY1GridRightCLocalCoverCode selected labelAt pointAt tubeAt
            ballRadius a) < ballRadius := by
      simpa only [actualY1GridRightCLocalCoverCode,
        actualY1GridRightCLocalCoverSourceTube,
        actualY1RightCLocalCoverCode,
        actualY1RightCLocalCoverSourceTube, r] using hcover
    rw [hcoverEq] at hcover'
    exact hcover'
  have hlocal := exactLocal_centeredTube_mem_approxCommonC_c2Ball
    (tubeAt (pointAt r)) coverCenter c f f1 f2 hfDeriv hf1Deriv
      outerA outerB hOuter (pointAt r).2 fineDelta fineScale
      localDelta (4 * ballRadius) ballRadius (3 * (radius : Real) / 2)
      hcoverDistance.le hcError hparameter hfunction hfirst hsecond
  have hbudget := approximateCommonCLocalC2Radius_le_twelve ballRadius
    (3 * (radius : Real) / 2) hballRadius.le hcBudget
  intro z hz
  have hzLocal := hlocal z hz
  simpa only [actualY1GridRightCLocalCoverExactLocalRectangle,
    actualY1RightCLocalCoverExactLocalRectangle,
    y1FineCoarseRectangleData, r] using
      ⟨hzLocal.1.trans hbudget, hzLocal.2.1.trans hbudget,
        hzLocal.2.2.trans hbudget⟩

#print axioms actualY1GridRightCLocalCover_selected_card_eq_sum_fiber_card
#print axioms pairwiseDisjoint_actualY1GridRightCLocalCoverFiber
#print axioms three_halves_radius_le_eight_ballRadius_of_cNormalizedThreeShiftSmall
#print axioms actualY1GridRightCLocalCoverFiber_hballLocal

end

end FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
