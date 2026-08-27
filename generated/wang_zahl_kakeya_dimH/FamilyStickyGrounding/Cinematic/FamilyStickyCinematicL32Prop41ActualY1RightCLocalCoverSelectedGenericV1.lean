import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteValueFibresV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set
open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32FiniteValueFibresV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v w

/-!
# Package-free right-C/local-cover refinement

The only carrier data are a finite selected set, its genuine fine label, and
its right tube index.  Consequently this module can be instantiated by the
C-normalized label-first package without mentioning the obsolete global
fixed-C package.
-/

abbrev ActualY1RightCLocalCoverSelectedItem
    {item : Type u} [DecidableEq item] (selected : Finset item) :=
  {a : item // a ∈ selected}

def actualY1RightCLocalCoverSourceTube
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) :
    ActualY1RightCLocalCoverSelectedItem selected -> Tube radius :=
  fun a => tubeAt (pointAt (labelAt a.1))

def actualY1RightCLocalCoverRightC
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (rightIndex : item -> iota) :
    ActualY1RightCLocalCoverSelectedItem selected -> Real :=
  fun a => tubeGraphC (fine.tubes (rightIndex a.1))

noncomputable def actualY1RightCLocalCoverCode
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    ActualY1RightCLocalCoverSelectedItem selected -> Tube radius :=
  finiteTubeCoefficientCoverCode
    (actualY1RightCLocalCoverSourceTube selected labelAt pointAt tubeAt)
    ballRadius

noncomputable def actualY1RightCLocalCoverValue
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    ActualY1RightCLocalCoverSelectedItem selected -> Real × Tube radius :=
  fun a =>
    (actualY1RightCLocalCoverRightC fine selected rightIndex a,
      actualY1RightCLocalCoverCode selected labelAt pointAt tubeAt
        ballRadius a)

noncomputable def actualY1RightCLocalCoverFiber
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius) :
    Finset (ActualY1RightCLocalCoverSelectedItem selected) :=
  finiteValueFiber Finset.univ
    (actualY1RightCLocalCoverValue fine selected labelAt rightIndex pointAt
      tubeAt ballRadius) value

noncomputable def actualY1RightCLocalCoverValues
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    Finset (Real × Tube radius) :=
  finiteOccupiedValues Finset.univ
    (actualY1RightCLocalCoverValue fine selected labelAt rightIndex pointAt
      tubeAt ballRadius)

noncomputable def actualY1RightCLocalCoverUnderlyingFiber
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius) : Finset item :=
  (actualY1RightCLocalCoverFiber fine selected labelAt rightIndex pointAt
    tubeAt ballRadius value).image Subtype.val

def actualY1RightCLocalCoverExactLocalRectangle
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u}
    {fineLabel : Type v} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (labelAt : item -> fineLabel) (localDelta localScale : Real) :
    item -> C2GraphRectangle :=
  fun a => exactLocalC2GraphRectangle (D.fineRectangleAt (labelAt a))
    localDelta localScale

theorem actualY1RightCLocalCoverFiber_nonempty
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius)
    (hvalue : value ∈ actualY1RightCLocalCoverValues fine selected labelAt
      rightIndex pointAt tubeAt ballRadius) :
    (actualY1RightCLocalCoverFiber fine selected labelAt rightIndex pointAt
      tubeAt ballRadius value).Nonempty :=
  finiteValueFiber_nonempty_of_mem Finset.univ
    (actualY1RightCLocalCoverValue fine selected labelAt rightIndex pointAt
      tubeAt ballRadius) hvalue

theorem actualY1RightCLocalCoverUnderlyingFiber_subset
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius) :
    actualY1RightCLocalCoverUnderlyingFiber fine selected labelAt rightIndex
      pointAt tubeAt ballRadius value ⊆ selected := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨b, _hb, rfl⟩
  exact b.2

theorem actualY1RightCLocalCoverUnderlyingFiber_nonempty
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius)
    (hvalue : value ∈ actualY1RightCLocalCoverValues fine selected labelAt
      rightIndex pointAt tubeAt ballRadius) :
    (actualY1RightCLocalCoverUnderlyingFiber fine selected labelAt rightIndex
      pointAt tubeAt ballRadius value).Nonempty := by
  rcases actualY1RightCLocalCoverFiber_nonempty fine selected labelAt
    rightIndex pointAt tubeAt ballRadius value hvalue with ⟨a, ha⟩
  exact ⟨a.1, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩

theorem actualY1RightCLocalCoverUnderlyingFiber_card
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius) :
    (actualY1RightCLocalCoverUnderlyingFiber fine selected labelAt rightIndex
      pointAt tubeAt ballRadius value).card =
      (actualY1RightCLocalCoverFiber fine selected labelAt rightIndex pointAt
        tubeAt ballRadius value).card := by
  unfold actualY1RightCLocalCoverUnderlyingFiber
  exact Finset.card_image_of_injective _ Subtype.val_injective

theorem actualY1RightCLocalCover_selected_card_eq_sum_fiber_card
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    selected.card =
      ∑ value ∈ actualY1RightCLocalCoverValues fine selected labelAt
        rightIndex pointAt tubeAt ballRadius,
        (actualY1RightCLocalCoverFiber fine selected labelAt rightIndex pointAt
          tubeAt ballRadius value).card := by
  rw [← Fintype.card_coe selected]
  simpa only [Finset.card_univ, actualY1RightCLocalCoverValues,
    actualY1RightCLocalCoverFiber] using
      card_eq_sum_finiteValueFiber_card
        (Finset.univ : Finset
          (ActualY1RightCLocalCoverSelectedItem selected))
        (actualY1RightCLocalCoverValue fine selected labelAt rightIndex pointAt
          tubeAt ballRadius)

theorem actualY1RightCLocalCoverFiber_rightGraphC
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius) (a : ActualY1RightCLocalCoverSelectedItem selected)
    (ha : a ∈ actualY1RightCLocalCoverFiber fine selected labelAt rightIndex
      pointAt tubeAt ballRadius (c, coverCenter)) :
    tubeGraphC (fine.tubes (rightIndex a.1)) = c := by
  have haValue := (mem_finiteValueFiber_iff Finset.univ
    (actualY1RightCLocalCoverValue fine selected labelAt rightIndex pointAt
      tubeAt ballRadius) (c, coverCenter) a).mp ha |>.2
  simpa only [actualY1RightCLocalCoverValue,
    actualY1RightCLocalCoverRightC] using congrArg Prod.fst haValue

theorem actualY1RightCLocalCoverUnderlyingFiber_rightGraphC
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius) :
    forall a, a ∈ actualY1RightCLocalCoverUnderlyingFiber fine selected
      labelAt rightIndex pointAt tubeAt ballRadius (c, coverCenter) ->
      tubeGraphC (fine.tubes (rightIndex a)) = c := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
  exact actualY1RightCLocalCoverFiber_rightGraphC fine selected labelAt
    rightIndex pointAt tubeAt ballRadius c coverCenter b hb

/-- A per-pair C-normalization transports the fibre's right-C value to the
left tube used by a counting package. -/
theorem actualY1RightCLocalCoverUnderlyingFiber_leftGraphC_of_pair
    {radius : NNReal} {iota : Type w} [DecidableEq iota]
    {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius) (leftTube : item -> Tube radius)
    (hpair : forall a, a ∈ selected ->
      tubeGraphC (leftTube a) = tubeGraphC (fine.tubes (rightIndex a))) :
    forall a, a ∈ actualY1RightCLocalCoverUnderlyingFiber fine selected
      labelAt rightIndex pointAt tubeAt ballRadius (c, coverCenter) ->
      tubeGraphC (leftTube a) = c := by
  intro a ha
  exact (hpair a
    (actualY1RightCLocalCoverUnderlyingFiber_subset fine selected labelAt
      rightIndex pointAt tubeAt ballRadius (c, coverCenter) ha)).trans
        (actualY1RightCLocalCoverUnderlyingFiber_rightGraphC fine selected
          labelAt rightIndex pointAt tubeAt ballRadius c coverCenter a ha)

theorem actualY1RightCLocalCoverUnderlyingFiber_forall
    {radius : NNReal} {iota : Type w} [DecidableEq iota] {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real)
    (value : Real × Tube radius) (Q : item -> Prop)
    (hQ : forall a, a ∈ actualY1RightCLocalCoverFiber fine selected labelAt
      rightIndex pointAt tubeAt ballRadius value -> Q a.1) :
    forall a, a ∈ actualY1RightCLocalCoverUnderlyingFiber fine selected
      labelAt rightIndex pointAt tubeAt ballRadius value -> Q a := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
  exact hQ b hb

theorem actualY1RightCLocalCoverFiber_coverCode_eq
    {radius : NNReal} {iota : Type w} [DecidableEq iota]
    {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightIndex : item -> iota) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius) (a : ActualY1RightCLocalCoverSelectedItem selected)
    (ha : a ∈ actualY1RightCLocalCoverFiber fine selected labelAt rightIndex
      pointAt tubeAt ballRadius (c, coverCenter)) :
    actualY1RightCLocalCoverCode selected labelAt pointAt tubeAt ballRadius a =
      coverCenter := by
  have haValue := (mem_finiteValueFiber_iff Finset.univ
    (actualY1RightCLocalCoverValue fine selected labelAt rightIndex pointAt
      tubeAt ballRadius) (c, coverCenter) a).mp ha |>.2
  simpa only [actualY1RightCLocalCoverValue] using congrArg Prod.snd haValue

/-! ## Actual Y1 geometry -/

/-- The package-free local ball producer.  The right retained incidence
supplies active membership and hence the c-bucket error; the finite source
cover supplies the reduced coefficient distance. -/
theorem actualY1RightCLocalCoverFiber_hballLocal
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
    (rightIndex : item -> iota)
    (hrightRetained : forall a, a ∈ selected ->
      (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep)
    (localDelta ballRadius : Real)
    (hballRadius : 0 < ballRadius)
    (hcBudget : (radius : Real) / 2 <= 8 * ballRadius)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (c : Real) (coverCenter : Tube radius) :
    forall a,
      a ∈ actualY1RightCLocalCoverFiber fine selected labelAt rightIndex
        pointAt tubeAt ballRadius (c, coverCenter) ->
      InPointwiseC2BallOn (Icc outerA outerB)
        (globalCenterFixedCommonCReference coverCenter c f f1 f2
          hfDeriv hf1Deriv outerA outerB hOuter)
        (actualY1RightCLocalCoverExactLocalRectangle D labelAt localDelta
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
  have hcEndpoint : tubeGraphC (fine.tubes i) = c := by
    simpa only [i] using
      actualY1RightCLocalCoverFiber_rightGraphC fine selected labelAt
        rightIndex pointAt tubeAt ballRadius c coverCenter a ha
  have hcRaw := facts.hactiveCBucket (pointAt r) hqE i hactiveData.2.1
  have hcError : |tubeGraphC (tubeAt (pointAt r)) - c| <=
      (radius : Real) / 2 := by
    rw [← hcEndpoint, abs_sub_comm]
    exact hcRaw
  have hcoverEq :
      actualY1RightCLocalCoverCode selected labelAt pointAt tubeAt ballRadius a =
        coverCenter :=
    actualY1RightCLocalCoverFiber_coverCode_eq fine selected labelAt rightIndex
      pointAt tubeAt ballRadius c coverCenter a ha
  have hcoverDistance :
      tubePairCoefficientDistance (tubeAt (pointAt r)) coverCenter <
        ballRadius := by
    have hcover := sourceTube_distance_coverCode_lt
      (actualY1RightCLocalCoverSourceTube selected labelAt pointAt tubeAt)
      ballRadius hballRadius a
    have hcover' :
        tubePairCoefficientDistance (tubeAt (pointAt r))
          (actualY1RightCLocalCoverCode selected labelAt pointAt tubeAt
            ballRadius a) < ballRadius := by
      simpa only [actualY1RightCLocalCoverCode,
        actualY1RightCLocalCoverSourceTube, r] using hcover
    rw [hcoverEq] at hcover'
    exact hcover'
  have hlocal := exactLocal_centeredTube_mem_approxCommonC_c2Ball
    (tubeAt (pointAt r)) coverCenter c f f1 f2 hfDeriv hf1Deriv
      outerA outerB hOuter (pointAt r).2 fineDelta fineScale
      localDelta (4 * ballRadius) ballRadius ((radius : Real) / 2)
      hcoverDistance.le hcError hparameter hfunction hfirst hsecond
  have hbudget := approximateCommonCLocalC2Radius_le_twelve ballRadius
    ((radius : Real) / 2) hballRadius.le hcBudget
  intro z hz
  have hzLocal := hlocal z hz
  simpa only [actualY1RightCLocalCoverExactLocalRectangle,
    y1FineCoarseRectangleData, r] using
      ⟨hzLocal.1.trans hbudget, hzLocal.2.1.trans hbudget,
        hzLocal.2.2.trans hbudget⟩

#print axioms actualY1RightCLocalCoverFiber_hballLocal

end

end FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
