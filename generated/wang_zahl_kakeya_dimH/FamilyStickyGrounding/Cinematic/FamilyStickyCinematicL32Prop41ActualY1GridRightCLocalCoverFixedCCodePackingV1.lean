import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

namespace FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverFixedCCodePackingV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Packing the source-cover codes used inside a fixed normalized-C fibre

The maximal cover is built once from all selected source tubes.  We first
pack the entire set of actually assigned source-cover codes; the code set
inside one fixed normalized-C fibre is a subset.  Thus the packing cap does
not count transformed endpoint tubes and introduces no endpoint
multiplicity.
-/

/-- Every source-cover code actually assigned to a selected item. -/
noncomputable def actualY1GridRightCLocalCoverSourceCodes
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    Finset (Tube radius) :=
  Finset.univ.image
    (actualY1GridRightCLocalCoverCode selected labelAt pointAt tubeAt
      ballRadius)

/-- The exact occupied source-cover code set over one literal normalized C.
This is the second-coordinate image of the occupied `(C, code)` values after
filtering on the first coordinate. -/
noncomputable def actualY1GridRightCLocalCoverSourceCodesAtC
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real) :
    Finset (Tube radius) :=
  ((actualY1GridRightCLocalCoverValues selected labelAt rightTube pointAt
      tubeAt ballRadius).filter fun value => value.1 = c).image Prod.snd

theorem mem_actualY1GridRightCLocalCoverSourceCodesAtC_iff
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real)
    (coverCenter : Tube radius) :
    coverCenter ∈ actualY1GridRightCLocalCoverSourceCodesAtC selected
      labelAt rightTube pointAt tubeAt ballRadius c ↔
      (c, coverCenter) ∈ actualY1GridRightCLocalCoverValues selected labelAt
        rightTube pointAt tubeAt ballRadius := by
  simp only [actualY1GridRightCLocalCoverSourceCodesAtC, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨c', code⟩, ⟨hvalue, hc'⟩, hcode⟩
    change c' = c at hc'
    change code = coverCenter at hcode
    subst c'
    subst code
    exact hvalue
  · intro hvalue
    exact ⟨(c, coverCenter), ⟨hvalue, rfl⟩, rfl⟩

/-- The fixed-C code set is contained in the set of all actually assigned
source-cover codes. -/
theorem actualY1GridRightCLocalCoverSourceCodesAtC_subset_sourceCodes
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius c : Real) :
    actualY1GridRightCLocalCoverSourceCodesAtC selected labelAt rightTube
      pointAt tubeAt ballRadius c ⊆
      actualY1GridRightCLocalCoverSourceCodes selected labelAt pointAt tubeAt
        ballRadius := by
  intro coverCenter hcoverCenter
  have hvalue :=
    (mem_actualY1GridRightCLocalCoverSourceCodesAtC_iff selected labelAt
      rightTube pointAt tubeAt ballRadius c coverCenter).mp hcoverCenter
  rcases actualY1GridRightCLocalCoverFiber_nonempty selected labelAt rightTube
    pointAt tubeAt ballRadius (c, coverCenter) hvalue with ⟨a, ha⟩
  have hcode := actualY1GridRightCLocalCoverFiber_coverCode_eq selected
    labelAt rightTube pointAt tubeAt ballRadius c coverCenter a ha
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hcode⟩

/-- Every actually assigned code is one of the centres of the single
maximal source-tube cover. -/
theorem actualY1GridRightCLocalCoverSourceCodes_subset_coverCenters
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    actualY1GridRightCLocalCoverSourceCodes selected labelAt pointAt tubeAt
      ballRadius ⊆
      finiteMetricCoverCenters
        (finiteTubeCoefficientCoverFamily
          (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt
            tubeAt))
        tubePairCoefficientDistance ballRadius
          tubePairCoefficientDistance_comm := by
  intro coverCenter hcoverCenter
  rcases Finset.mem_image.mp hcoverCenter with ⟨a, _ha, rfl⟩
  simpa only [actualY1GridRightCLocalCoverCode,
    actualY1RightCLocalCoverCode,
    actualY1GridRightCLocalCoverSourceTube,
    actualY1RightCLocalCoverSourceTube,
    finiteTubeCoefficientCoverCode] using
      finiteMetricCoverCode_mem_centers
        (finiteTubeCoefficientCoverFamily
          (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt
            tubeAt))
        tubePairCoefficientDistance ballRadius
          tubePairCoefficientDistance_comm
        (finiteTubeCoefficientCoverMember
          (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt
            tubeAt) a)

/-- The actual assigned source-cover codes inherit `ballRadius` separation
in the projected coefficient metric. -/
theorem actualY1GridRightCLocalCoverSourceCodes_pairwise_separated
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (ballRadius : Real) :
    forall T, T ∈ actualY1GridRightCLocalCoverSourceCodes selected labelAt
      pointAt tubeAt ballRadius ->
      forall U, U ∈ actualY1GridRightCLocalCoverSourceCodes selected
        labelAt pointAt tubeAt ballRadius -> T ≠ U ->
        ballRadius <= projectedTubePairCoefficientDistance T U := by
  intro T hT U hU hTU
  have hsep := finiteMetricCoverCenters_pairwise_separated
    (finiteTubeCoefficientCoverFamily
      (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt tubeAt))
    tubePairCoefficientDistance ballRadius tubePairCoefficientDistance_comm
    T
    (actualY1GridRightCLocalCoverSourceCodes_subset_coverCenters selected
      labelAt pointAt tubeAt ballRadius hT)
    U
    (actualY1GridRightCLocalCoverSourceCodes_subset_coverCenters selected
      labelAt pointAt tubeAt ballRadius hU) hTU
  simpa only [tubePairCoefficientDistance_eq_projected] using hsep

/-- If every selected source lies in a closed `sourceRadius` coefficient
ball, then every actually assigned code lies in the open sum-radius ball. -/
theorem actualY1GridRightCLocalCoverSourceCode_distance_globalCenter_lt_add
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (ballRadius : Real) (hballRadius : 0 < ballRadius)
    (globalCenter : Tube radius) (sourceRadius : Real)
    (hsource : forall a : ActualY1GridRightCLocalCoverSelectedItem selected,
      tubePairCoefficientDistance
        (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt
          tubeAt a) globalCenter <= sourceRadius)
    (coverCenter : Tube radius)
    (hcoverCenter : coverCenter ∈
      actualY1GridRightCLocalCoverSourceCodes selected labelAt pointAt tubeAt
        ballRadius) :
    tubePairCoefficientDistance coverCenter globalCenter <
      ballRadius + sourceRadius := by
  rcases Finset.mem_image.mp hcoverCenter with ⟨a, _ha, rfl⟩
  have hcover := sourceTube_distance_coverCode_lt
    (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt tubeAt)
    ballRadius hballRadius a
  have hcover' : tubePairCoefficientDistance
      (actualY1GridRightCLocalCoverCode selected labelAt pointAt tubeAt
        ballRadius a)
      (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt tubeAt
        a) < ballRadius := by
    rw [tubePairCoefficientDistance_comm]
    simpa only [actualY1GridRightCLocalCoverCode,
      actualY1RightCLocalCoverCode,
      actualY1GridRightCLocalCoverSourceTube,
      actualY1RightCLocalCoverSourceTube] using hcover
  have htriangle := tubePairCoefficientDistance_triangle
    (actualY1GridRightCLocalCoverCode selected labelAt pointAt tubeAt
      ballRadius a) globalCenter
    (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt tubeAt a)
  linarith [hsource a]

/-- All assigned codes survive the strict projected ball filter of radius
twice `ballRadius + sourceRadius`. -/
theorem actualY1GridRightCLocalCoverSourceCodes_filter_eq_self
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (ballRadius : Real) (hballRadius : 0 < ballRadius)
    (globalCenter : Tube radius) (sourceRadius : Real)
    (hsource : forall a : ActualY1GridRightCLocalCoverSelectedItem selected,
      tubePairCoefficientDistance
        (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt
          tubeAt a) globalCenter <= sourceRadius)
    (hpositive : 0 < ballRadius + sourceRadius) :
    (actualY1GridRightCLocalCoverSourceCodes selected labelAt pointAt tubeAt
      ballRadius).filter (fun T =>
        projectedTubePairCoefficientDistance T globalCenter <
          2 * (ballRadius + sourceRadius)) =
      actualY1GridRightCLocalCoverSourceCodes selected labelAt pointAt tubeAt
        ballRadius := by
  apply Finset.filter_eq_self.mpr
  intro coverCenter hcoverCenter
  have hlt :=
    actualY1GridRightCLocalCoverSourceCode_distance_globalCenter_lt_add
      selected labelAt pointAt tubeAt ballRadius hballRadius globalCenter
        sourceRadius hsource coverCenter hcoverCenter
  rw [← tubePairCoefficientDistance_eq_projected]
  linarith

/-- Honest packing cap for all assigned source-cover codes. -/
theorem actualY1GridRightCLocalCoverSourceCodes_card_lt_packingCap
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (ballRadius : Real) (hballRadius : 0 < ballRadius)
    (globalCenter : Tube radius) (sourceRadius : Real)
    (hsource : forall a : ActualY1GridRightCLocalCoverSelectedItem selected,
      tubePairCoefficientDistance
        (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt
          tubeAt a) globalCenter <= sourceRadius)
    (hpositive : 0 < ballRadius + sourceRadius) :
    (actualY1GridRightCLocalCoverSourceCodes selected labelAt pointAt tubeAt
      ballRadius).card <
      projectedCoefficientPackingCap ballRadius
        (2 * (ballRadius + sourceRadius)) := by
  have hpack := projectedCoefficientBall_card_lt_packingCap
    (actualY1GridRightCLocalCoverSourceCodes selected labelAt pointAt tubeAt
      ballRadius) (separation := ballRadius)
        (bound := 2 * (ballRadius + sourceRadius)) hballRadius
    (actualY1GridRightCLocalCoverSourceCodes_pairwise_separated selected
      labelAt pointAt tubeAt ballRadius) globalCenter
  rw [actualY1GridRightCLocalCoverSourceCodes_filter_eq_self selected labelAt
    pointAt tubeAt ballRadius hballRadius globalCenter sourceRadius hsource
      hpositive] at hpack
  exact hpack

/-- The fixed-C occupied code set obeys the same cap. -/
theorem actualY1GridRightCLocalCoverSourceCodesAtC_card_lt_packingCap
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (ballRadius : Real) (hballRadius : 0 < ballRadius)
    (globalCenter : Tube radius) (sourceRadius : Real)
    (hsource : forall a : ActualY1GridRightCLocalCoverSelectedItem selected,
      tubePairCoefficientDistance
        (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt
          tubeAt a) globalCenter <= sourceRadius)
    (hpositive : 0 < ballRadius + sourceRadius) (c : Real) :
    (actualY1GridRightCLocalCoverSourceCodesAtC selected labelAt rightTube
      pointAt tubeAt ballRadius c).card <
      projectedCoefficientPackingCap ballRadius
        (2 * (ballRadius + sourceRadius)) := by
  exact lt_of_le_of_lt
    (Finset.card_le_card
      (actualY1GridRightCLocalCoverSourceCodesAtC_subset_sourceCodes selected
        labelAt rightTube pointAt tubeAt ballRadius c))
    (actualY1GridRightCLocalCoverSourceCodes_card_lt_packingCap selected
      labelAt pointAt tubeAt ballRadius hballRadius globalCenter sourceRadius
        hsource hpositive)

/-- The concrete source localization used by Family 7. -/
theorem actualY1GridRightCLocalCoverSourceCodesAtC_card_lt_packingCap_six_mul
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (ballRadius : Real) (hballRadius : 0 < ballRadius)
    (globalCenter : Tube radius) (tGlobal : Real)
    (hsource : forall a : ActualY1GridRightCLocalCoverSelectedItem selected,
      tubePairCoefficientDistance
        (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt
          tubeAt a) globalCenter <= 6 * tGlobal)
    (hpositive : 0 < ballRadius + 6 * tGlobal) (c : Real) :
    (actualY1GridRightCLocalCoverSourceCodesAtC selected labelAt rightTube
      pointAt tubeAt ballRadius c).card <
      projectedCoefficientPackingCap ballRadius
        (2 * (ballRadius + 6 * tGlobal)) := by
  exact actualY1GridRightCLocalCoverSourceCodesAtC_card_lt_packingCap selected
    labelAt rightTube pointAt tubeAt ballRadius hballRadius globalCenter
      (6 * tGlobal) hsource hpositive c

/-- A centered-half point source discharges the concrete `6 * tGlobal`
source localization once every selected label points into its source set. -/
theorem actualY1GridRightCLocalCoverSourceTube_distance_globalCenter_le_six_mul_of_pointSource
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (E : Set (Real × Real)) (globalCenter : Tube radius)
    (tubeAt : Real × Real -> Tube radius) (f : Real -> Real)
    (outerA outerB tGlobal : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource E globalCenter
      tubeAt f outerA outerB tGlobal)
    (hlabel : forall a, a ∈ selected -> labelAt a ∈ fineLabels)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E) :
    forall a : ActualY1GridRightCLocalCoverSelectedItem selected,
      tubePairCoefficientDistance
        (actualY1GridRightCLocalCoverSourceTube selected labelAt pointAt
          tubeAt a) globalCenter <= 6 * tGlobal := by
  intro a
  rw [tubePairCoefficientDistance_comm]
  exact pointSource.hcoefficientUpper (pointAt (labelAt a.1))
    (hpointE (labelAt a.1) (hlabel a.1 a.2))

/-- Fully grounded fixed-C code cap from the actual centered-half point
source, with no separate coefficient-localization hypothesis. -/
theorem actualY1GridRightCLocalCoverSourceCodesAtC_card_lt_packingCap_of_pointSource
    {radius : NNReal} {item : Type u} [DecidableEq item]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (selected : Finset item) (labelAt : item -> fineLabel)
    (rightTube : item -> Tube radius)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (E : Set (Real × Real)) (globalCenter : Tube radius)
    (tubeAt : Real × Real -> Tube radius) (f : Real -> Real)
    (outerA outerB tGlobal ballRadius : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource E globalCenter
      tubeAt f outerA outerB tGlobal)
    (hlabel : forall a, a ∈ selected -> labelAt a ∈ fineLabels)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (hballRadius : 0 < ballRadius)
    (hpositive : 0 < ballRadius + 6 * tGlobal) (c : Real) :
    (actualY1GridRightCLocalCoverSourceCodesAtC selected labelAt rightTube
      pointAt tubeAt ballRadius c).card <
      projectedCoefficientPackingCap ballRadius
        (2 * (ballRadius + 6 * tGlobal)) := by
  exact
    actualY1GridRightCLocalCoverSourceCodesAtC_card_lt_packingCap_six_mul
      selected labelAt rightTube pointAt tubeAt ballRadius hballRadius
        globalCenter tGlobal
        (actualY1GridRightCLocalCoverSourceTube_distance_globalCenter_le_six_mul_of_pointSource
          selected labelAt fineLabels pointAt E globalCenter tubeAt f outerA
            outerB tGlobal pointSource hlabel hpointE)
        hpositive c

#print axioms actualY1GridRightCLocalCoverSourceCodesAtC_card_lt_packingCap_of_pointSource

#print axioms actualY1GridRightCLocalCoverSourceCodes_subset_coverCenters
#print axioms actualY1GridRightCLocalCoverSourceCodes_filter_eq_self
#print axioms actualY1GridRightCLocalCoverSourceCodesAtC_card_lt_packingCap_six_mul

end

end FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverFixedCCodePackingV1
