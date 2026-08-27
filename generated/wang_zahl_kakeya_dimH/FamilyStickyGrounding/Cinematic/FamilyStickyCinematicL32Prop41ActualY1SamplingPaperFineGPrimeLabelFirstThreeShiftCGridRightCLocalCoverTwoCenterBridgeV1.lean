import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverFixedCCodePackingV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SharpCommonCReferenceTwoCenterBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverTwoCenterBridgeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverFixedCCodePackingV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceTwoCenterBridgeV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Actual source/global two-centre bridge after shifted C-grid normalization

The local-cover code still comes from the fine rectangle's source tube
`tubeAt (pointAt (labelAt a))`; the shifted-grid final right tube is used
only for the literal outer C key.  Consequently the source-to-global bound
comes directly from the retained label and the centered-half point source,
with no count of normalized endpoint copies.
-/

def actualGPrimeThreeShiftCGridRightCLocalCoverSourceTube
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) :
    ActualY1GridRightCLocalCoverSelectedItem P.selected -> Tube radius :=
  actualY1GridRightCLocalCoverSourceTube P.selected
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    pointAt tubeAt

noncomputable def actualGPrimeThreeShiftCGridRightCLocalCoverValues
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) : Finset (Real × Tube radius) :=
  actualY1GridRightCLocalCoverValues P.selected
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
      ballRadius omega P.gridLabel)
    pointAt tubeAt ballRadius

noncomputable def actualGPrimeThreeShiftCGridRightCLocalCoverFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (value : Real × Tube radius) :
    Finset (ActualY1GridRightCLocalCoverSelectedItem P.selected) :=
  actualY1GridRightCLocalCoverFiber P.selected
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
      ballRadius omega P.gridLabel)
    pointAt tubeAt ballRadius value

/-- Every selected source tube is honestly localized at coefficient distance
at most `6 * tGlobal` from the literal global centre. -/
theorem actualGPrimeThreeShiftCGridRightCLocalCoverSourceTube_distance_globalCenter_le
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (globalCenter : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource E globalCenter
      tubeAt f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (fineDelta fineScale coarseDelta coarseScale : Real)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (globalDelta : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (a : ActualY1GridRightCLocalCoverSelectedItem P.selected) :
    tubePairCoefficientDistance
      (actualGPrimeThreeShiftCGridRightCLocalCoverSourceTube fine N D keep
        left right ballRadius omega f outerA outerB globalDelta tGlobal P
          pointAt tubeAt a)
      globalCenter <= 6 * tGlobal := by
  subst D
  let r := actualGPrimeLabelFirstLabel N
    (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
    keep left right ballRadius omega a.1
  let i := actualGPrimeLabelFirstRightIndex N
    (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
    keep left right ballRadius omega a.1
  have hretained := P.right_retained a.1 a.2
  have hactiveData := y1FineCoarseRectangleData_retainedPair_active fine Y1
    fineLabels pointAt tubeAt f f1 f2 hfDeriv hf1Deriv fineDelta fineScale
      coarseDelta coarseScale keep i r hretained
  have hqE : pointAt r ∈ E := hpointE r hactiveData.1
  change tubePairCoefficientDistance (tubeAt (pointAt r)) globalCenter <=
    6 * tGlobal
  rw [tubePairCoefficientDistance_comm]
  exact pointSource.hcoefficientUpper (pointAt r) hqE

/-- Every occupied grid-right-C/local-cover centre is within the sum of the
cover radius and the actual source localization radius. -/
theorem actualGPrimeThreeShiftCGridRightCLocalCoverFiber_coverCenter_distance_globalCenter_le
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (globalCenter : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource E globalCenter
      tubeAt f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (fineDelta fineScale coarseDelta coarseScale : Real)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (hballRadius : 0 < ballRadius)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (globalDelta : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (c : Real) (coverCenter : Tube radius)
    (a : ActualY1GridRightCLocalCoverSelectedItem P.selected)
    (ha : a ∈ actualGPrimeThreeShiftCGridRightCLocalCoverFiber fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal P
        pointAt tubeAt (c, coverCenter)) :
    tubePairCoefficientDistance coverCenter globalCenter <=
      ballRadius + 6 * tGlobal := by
  have ha' : a ∈ actualY1GridRightCLocalCoverFiber P.selected
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
        ballRadius omega P.gridLabel)
      pointAt tubeAt ballRadius (c, coverCenter) := by
    simpa only [actualGPrimeThreeShiftCGridRightCLocalCoverFiber] using ha
  have hcode := actualY1GridRightCLocalCoverFiber_coverCode_eq P.selected
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
      ballRadius omega P.gridLabel)
    pointAt tubeAt ballRadius c coverCenter a ha'
  have hcodeMem : coverCenter ∈
      actualY1GridRightCLocalCoverSourceCodes P.selected
        (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
        pointAt tubeAt ballRadius :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hcode⟩
  have hsource : forall b : ActualY1GridRightCLocalCoverSelectedItem P.selected,
      tubePairCoefficientDistance
        (actualY1GridRightCLocalCoverSourceTube P.selected
          (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
          pointAt tubeAt b) globalCenter <= 6 * tGlobal := by
    intro b
    exact actualGPrimeThreeShiftCGridRightCLocalCoverSourceTube_distance_globalCenter_le
      fine E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2 outerA outerB
        hfDeriv hf1Deriv tGlobal pointSource hpointE fineDelta fineScale
          coarseDelta coarseScale N D hD keep left right ballRadius omega
            globalDelta P b
  exact
    (actualY1GridRightCLocalCoverSourceCode_distance_globalCenter_lt_add
      P.selected
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
      pointAt tubeAt ballRadius hballRadius globalCenter (6 * tGlobal)
        hsource coverCenter hcodeMem).le

/-- Exact second-jet bridge between the local cover reference and the global
reference sharing the fibre's literal normalized right-C value. -/
theorem actualGPrimeThreeShiftCGridRightCLocalCoverFiber_second_bridge
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (globalCenter : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource E globalCenter
      tubeAt f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (fineDelta fineScale coarseDelta coarseScale : Real)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (hballRadius : 0 < ballRadius)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (globalDelta : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (c : Real) (coverCenter : Tube radius)
    (hfiber : (actualGPrimeThreeShiftCGridRightCLocalCoverFiber fine N D keep
      left right ballRadius omega f outerA outerB globalDelta tGlobal P
        pointAt tubeAt (c, coverCenter)).Nonempty)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100) :
    forall z, z ∈ Icc outerA outerB ->
      |(globalCenterFixedCommonCReference coverCenter c f f1 f2
          hfDeriv hf1Deriv outerA outerB hOuter).second z -
        (globalCenterFixedCommonCReference globalCenter c f f1 f2
          hfDeriv hf1Deriv outerA outerB hOuter).second z| <=
        (401 / 100 : Real) * (ballRadius + 6 * tGlobal) := by
  rcases hfiber with ⟨a, ha⟩
  have hdistance :=
    actualGPrimeThreeShiftCGridRightCLocalCoverFiber_coverCenter_distance_globalCenter_le
      fine E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2 outerA outerB
        hfDeriv hf1Deriv tGlobal pointSource hpointE fineDelta fineScale
          coarseDelta coarseScale N D hD keep left right ballRadius
            hballRadius omega globalDelta P c coverCenter a ha
  exact globalCenterFixedCommonCReference_second_dist_le coverCenter
    globalCenter c f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter
      (ballRadius + 6 * tGlobal) hdistance hparameter hfunction hfirst hsecond

#print axioms actualGPrimeThreeShiftCGridRightCLocalCoverSourceTube_distance_globalCenter_le
#print axioms actualGPrimeThreeShiftCGridRightCLocalCoverFiber_coverCenter_distance_globalCenter_le
#print axioms actualGPrimeThreeShiftCGridRightCLocalCoverFiber_second_bridge

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverTwoCenterBridgeV1
