import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedEndpointC2BallV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32FiniteValuePairCarrierV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

section EndpointBall

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable {fineLabel : Type v} [DecidableEq fineLabel]
variable (fine : UniformTubeFamily radius iota)
variable (physical : FiniteProjectedShading (Real × Real) iota)
variable (tGlobal : Real) (globalCenter : Tube radius)
variable (N : CanonicalNormNonconcentrationData iota)
variable (D : CoarseRectangleIncidenceData (point := Real × Real)
  (radius := radius) (iota := iota) fineLabel)
variable (keep : iota -> fineLabel -> Prop) (left right : iota)
variable (ballRadius : Real)
variable (omega : (N.family -> Fin 1) × (N.family -> Fin 1))

private abbrev Survivor := ActualGPrimeLabelFirstSurvivor
  N D keep left right ballRadius omega

variable {items : Finset (Survivor N D keep left right ballRadius omega)}
variable {pairScale : Real}
variable (P : ActualRetainedY1ThreeShiftCGridSelection D items
  (actualGPrimeLabelFirstLeftIndex N D keep left right ballRadius omega)
  (actualGPrimeLabelFirstRightIndex N D keep left right ballRadius omega)
  (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
  keep pairScale)

/-- Every endpoint curve in an outer normalized-C fibre has that literal C
value.  Cover-code refinements must occur only inside this outer fibre. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_graphC
    {survivors : Finset (Survivor N D keep left right ballRadius omega)}
    (hsub : survivors ⊆ P.selected) (shift c : Real)
    {V : Tube radius}
    (hV : V ∈ actualThreeShiftCGridRestrictedTubeFamilyAt
      P survivors shift c) :
    tubeGraphC V = c := by
  simp only [actualThreeShiftCGridRestrictedTubeFamilyAt,
    finiteValuePairCarrierAt, finitePairCarrier, Finset.mem_union,
    Finset.mem_image] at hV
  rcases hV with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact (actualThreeShiftCGridRestrictedFiber_common_c
      P hsub shift c a (by
        simpa only [actualThreeShiftCGridRestrictedFiber] using ha)).1
  · exact (actualThreeShiftCGridRestrictedFiber_common_c
      P hsub shift c a (by
        simpa only [actualThreeShiftCGridRestrictedFiber] using ha)).2

/-- Membership in one outer C fibre automatically gives membership in the
deduplicated global final endpoint carrier. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_subset_global
    (survivors : Finset (Survivor N D keep left right ballRadius omega))
    (shift c : Real) :
    actualThreeShiftCGridRestrictedTubeFamilyAt P survivors shift c ⊆
      actualThreeShiftCGridRestrictedGlobalTubeFamily P survivors shift := by
  exact finiteValuePairCarrierAt_subset_global survivors
    (actualThreeShiftCGridRestrictedValueAt P shift)
    (actualThreeShiftCGridRestrictedTraceLeftTube P shift)
    (actualThreeShiftCGridRestrictedRightTube P) c

variable (f f1 f2 : Real -> Real)
variable (A B : Real) (hAB : A <= B)
variable (hfDeriv : forall z, HasDerivAt f (f1 z) z)
variable (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
variable (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
variable (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
variable (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
variable (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)

include hAB hparameter hfunction hfirst hsecond

/-- A final endpoint in one literal normalized-C fibre lies in the common
pointwise C2 ball of radius `approximateCommonCLocalC2Radius rho 0`, where
`rho = 3 * (tGlobal + |shift|)`. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_pairLocalReference_mem_c2Ball
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    {survivors : Finset (Survivor N D keep left right ballRadius omega)}
    (hsub : survivors ⊆ P.selected) (shift c : Real)
    (V : Tube radius)
    (hV : V ∈ actualThreeShiftCGridRestrictedTubeFamilyAt
      P survivors shift c) :
    InPointwiseC2BallOn (Icc A B)
      (globalCenterFixedCommonCReference globalCenter c f f1 f2
        hfDeriv hf1Deriv A B hAB)
      (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB)
      (approximateCommonCLocalC2Radius
        (actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
          tGlobal shift) 0) := by
  have hglobal : V ∈ actualThreeShiftCGridRestrictedGlobalTubeFamily
      P survivors shift :=
    actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_subset_global
      (N := N) (D := D) (keep := keep) (left := left) (right := right)
        (ballRadius := ballRadius) (omega := omega) (P := P)
          survivors shift c hV
  have hdistance :=
    actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_distance_le
      fine physical tGlobal globalCenter N D keep left right ballRadius omega
        P hDfine hfamily survivors shift V hglobal
  have hc :=
    actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_graphC
      (N := N) (D := D) (keep := keep) (left := left) (right := right)
        (ballRadius := ballRadius) (omega := omega) (P := P)
          hsub shift c hV
  apply pairLocalTubeReference_mem_approxCommonC_c2Ball
    V globalCenter c f f1 f2 hfDeriv hf1Deriv A B hAB
      (actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
        tGlobal shift) 0 hdistance
  · simp [hc]
  · exact hparameter
  · exact hfunction
  · exact hfirst
  · exact hsecond

/-- Endpoint-centred exact-local rectangle.  This is intentionally distinct
from `D.fineRectangleAt`: no equality is asserted unless a downstream source
map is explicitly built from the same final endpoint. -/
def actualGPrimeLabelFirstThreeShiftCGridEndpointExactLocalRectangle
    (V : Tube radius) (theta sourceDelta sourceScale delta localScale : Real) :
    C2GraphRectangle :=
  exactLocalC2GraphRectangle
    (centeredTubeC2GraphRectangle V f f1 f2 hfDeriv hf1Deriv
      theta sourceDelta sourceScale) delta localScale

/-- The same common C2-ball bound survives endpoint centring and exact-local
restriction, since these operations change only the rectangle base. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_endpointExactLocal_mem_c2Ball
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    {survivors : Finset (Survivor N D keep left right ballRadius omega)}
    (hsub : survivors ⊆ P.selected) (shift c : Real)
    (V : Tube radius)
    (hV : V ∈ actualThreeShiftCGridRestrictedTubeFamilyAt
      P survivors shift c)
    (theta sourceDelta sourceScale delta localScale : Real) :
    InPointwiseC2BallOn (Icc A B)
      (globalCenterFixedCommonCReference globalCenter c f f1 f2
        hfDeriv hf1Deriv A B hAB)
      (actualGPrimeLabelFirstThreeShiftCGridEndpointExactLocalRectangle
        (f := f) (f1 := f1) (f2 := f2) (hfDeriv := hfDeriv)
          (hf1Deriv := hf1Deriv) V theta sourceDelta sourceScale delta
            localScale)
      (approximateCommonCLocalC2Radius
        (actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
          tGlobal shift) 0) := by
  have hglobal : V ∈ actualThreeShiftCGridRestrictedGlobalTubeFamily
      P survivors shift :=
    actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_subset_global
      (N := N) (D := D) (keep := keep) (left := left) (right := right)
        (ballRadius := ballRadius) (omega := omega) (P := P)
          survivors shift c hV
  have hdistance :=
    actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_distance_le
      fine physical tGlobal globalCenter N D keep left right ballRadius omega
        P hDfine hfamily survivors shift V hglobal
  have hc :=
    actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_graphC
      (N := N) (D := D) (keep := keep) (left := left) (right := right)
        (ballRadius := ballRadius) (omega := omega) (P := P)
          hsub shift c hV
  simpa only [actualGPrimeLabelFirstThreeShiftCGridEndpointExactLocalRectangle]
    using exactLocal_centeredTube_mem_approxCommonC_c2Ball
      V globalCenter c f f1 f2 hfDeriv hf1Deriv A B hAB theta
        sourceDelta sourceScale delta localScale
        (actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
          tGlobal shift) 0 hdistance (by
            norm_num [hc]) hparameter hfunction hfirst
              hsecond

/-- Two endpoint-centred exact-local rectangles in one outer normalized-C
fibre have second-coordinate gap at most twice the honest common C2 radius. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_endpointExactLocal_second_gap
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    {survivors : Finset (Survivor N D keep left right ballRadius omega)}
    (hsub : survivors ⊆ P.selected) (shift c : Real)
    (V W : Tube radius)
    (hV : V ∈ actualThreeShiftCGridRestrictedTubeFamilyAt
      P survivors shift c)
    (hW : W ∈ actualThreeShiftCGridRestrictedTubeFamilyAt
      P survivors shift c)
    (thetaV thetaW sourceDelta sourceScale delta localScale z : Real)
    (hz : z ∈ Icc A B) :
    |(actualGPrimeLabelFirstThreeShiftCGridEndpointExactLocalRectangle
        (f := f) (f1 := f1) (f2 := f2) (hfDeriv := hfDeriv)
          (hf1Deriv := hf1Deriv) V thetaV sourceDelta sourceScale delta
            localScale).second z -
      (actualGPrimeLabelFirstThreeShiftCGridEndpointExactLocalRectangle
        (f := f) (f1 := f1) (f2 := f2) (hfDeriv := hfDeriv)
          (hf1Deriv := hf1Deriv) W thetaW sourceDelta sourceScale delta
            localScale).second z| <=
      2 * approximateCommonCLocalC2Radius
        (actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
          tGlobal shift) 0 := by
  apply abs_second_sub_le_two_mul_radius_of_mem_common_c2BallOn
    (actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_endpointExactLocal_mem_c2Ball
      fine physical tGlobal globalCenter N D keep left right ballRadius omega
        P f f1 f2 A B hAB hfDeriv hf1Deriv hparameter hfunction hfirst
          hsecond hDfine hfamily hsub shift c V hV thetaV sourceDelta
            sourceScale delta localScale)
    (actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_endpointExactLocal_mem_c2Ball
      fine physical tGlobal globalCenter N D keep left right ballRadius omega
        P f f1 f2 A B hAB hfDeriv hf1Deriv hparameter hfunction hfirst
          hsecond hDfine hfamily hsub shift c W hW thetaW sourceDelta
            sourceScale delta localScale)
    hz

end EndpointBall

#print axioms actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_graphC
#print axioms actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_pairLocalReference_mem_c2Ball
#print axioms actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_endpointExactLocal_mem_c2Ball
#print axioms actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_endpointExactLocal_second_gap

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedEndpointC2BallV1
