import FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
import FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TraceTangencyScaleUpperV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u

/-!
# Package-free approximate-common-C local-cover geometry

This module contains only analytic estimates, finite cover definitions, and
the paper-scale numerical consequence.  It has no sampling-package or
fixed-C provenance parameter.
-/

theorem pairLocalTubeReference_approxCommonC_jetBounds
    {radius : NNReal} (V globalCenter : Tube radius) (commonC : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho cError : Real)
    (hdistance : tubePairCoefficientDistance V globalCenter <= rho)
    (hcError : |tubeGraphC V - commonC| <= cError)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    forall z, z ∈ Icc A B ->
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).rectangle.graph z -
        (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).rectangle.graph z| <=
            2 * rho + cError ∧
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).first z -
        (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).first z| <=
            4 * rho + cError ∧
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).second z -
        (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).second z| <=
            (401 / 100 : Real) * rho := by
  intro z hz
  have hdistance' : coefficientDistance
      (tubePairDeltaA V globalCenter) (tubePairDeltaB V globalCenter)
        (tubePairDeltaD V globalCenter) <= rho := by
    simpa only [tubePairCoefficientDistance] using hdistance
  have hcErrorNonneg : 0 <= cError :=
    (abs_nonneg (tubeGraphC V - commonC)).trans hcError
  have hcLinear : |(tubeGraphC V - commonC) * z| <= cError := by
    rw [abs_mul]
    calc
      |tubeGraphC V - commonC| * |z| <= cError * |z| :=
        mul_le_mul_of_nonneg_right hcError (abs_nonneg z)
      _ <= cError * 1 :=
        mul_le_mul_of_nonneg_left (hparameter z hz) hcErrorNonneg
      _ = cError := by ring
  have hvalueRaw := abs_traceJet0_le_two_coefficientDistance
    (tubePairDeltaA V globalCenter) (tubePairDeltaB V globalCenter)
      (tubePairDeltaD V globalCenter) (f z) z
        (hparameter z hz) (hfunction z hz)
  have hfirstRaw := abs_traceJet1_le_four_coefficientDistance
    (tubePairDeltaA V globalCenter) (tubePairDeltaB V globalCenter)
      (tubePairDeltaD V globalCenter) (f z) (f1 z) z
        (hparameter z hz) (hfunction z hz) (hfirst z hz)
  have hsecondRaw := abs_traceJet2_le_401_div_100_coefficientDistance
    (tubePairDeltaA V globalCenter) (tubePairDeltaB V globalCenter)
      (tubePairDeltaD V globalCenter) (f1 z) (f2 z) z
        (hparameter z hz) (hfirst z hz) (hsecond z hz)
  constructor
  · calc
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).rectangle.graph z -
          (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
            hfDeriv hf1Deriv A B hAB).rectangle.graph z| =
          |traceJet0 (tubePairDeltaA V globalCenter)
              (tubePairDeltaB V globalCenter)
              (tubePairDeltaD V globalCenter) (f z) z +
            (tubeGraphC V - commonC) * z| := by
        simp only [pairLocalTubeReference, tubeC2GraphRectangle,
          globalCenterFixedCommonCReference, cinematicTraceValue,
          traceJet0, tubePairDeltaA, tubePairDeltaB, tubePairDeltaD]
        congr 1
        ring
      _ <= |traceJet0 (tubePairDeltaA V globalCenter)
              (tubePairDeltaB V globalCenter)
              (tubePairDeltaD V globalCenter) (f z) z| +
            |(tubeGraphC V - commonC) * z| := abs_add_le _ _
      _ <= 2 * coefficientDistance (tubePairDeltaA V globalCenter)
              (tubePairDeltaB V globalCenter)
              (tubePairDeltaD V globalCenter) + cError :=
        add_le_add hvalueRaw hcLinear
      _ <= 2 * rho + cError := by linarith
  constructor
  · calc
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).first z -
          (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
            hfDeriv hf1Deriv A B hAB).first z| =
          |traceJet1 (tubePairDeltaB V globalCenter)
              (tubePairDeltaD V globalCenter) (f z) (f1 z) z +
            (tubeGraphC V - commonC)| := by
        simp only [pairLocalTubeReference, tubeC2GraphRectangle,
          globalCenterFixedCommonCReference, tubeCinematicTraceFirstValue,
          cinematicTraceFirstValue, traceJet1, tubePairDeltaB,
          tubePairDeltaD]
        congr 1
        ring
      _ <= |traceJet1 (tubePairDeltaB V globalCenter)
              (tubePairDeltaD V globalCenter) (f z) (f1 z) z| +
            |tubeGraphC V - commonC| := abs_add_le _ _
      _ <= 4 * coefficientDistance (tubePairDeltaA V globalCenter)
              (tubePairDeltaB V globalCenter)
              (tubePairDeltaD V globalCenter) + cError :=
        add_le_add hfirstRaw hcError
      _ <= 4 * rho + cError := by linarith
  · calc
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).second z -
          (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
            hfDeriv hf1Deriv A B hAB).second z| =
          |traceJet2 (tubePairDeltaB V globalCenter)
              (tubePairDeltaD V globalCenter) (f1 z) (f2 z) z| := by
        simp only [pairLocalTubeReference, tubeC2GraphRectangle,
          globalCenterFixedCommonCReference, tubeCinematicTraceSecondValue,
          cinematicTraceSecondValue, traceJet2, tubePairDeltaB,
          tubePairDeltaD]
        congr 1
        ring
      _ <= (401 / 100 : Real) * coefficientDistance
          (tubePairDeltaA V globalCenter) (tubePairDeltaB V globalCenter)
            (tubePairDeltaD V globalCenter) := hsecondRaw
      _ <= (401 / 100 : Real) * rho := by nlinarith

/-- The exact radius required by the approximate-common-`c` source. -/
def approximateCommonCLocalC2Radius (rho cError : Real) : Real :=
  max ((401 / 100 : Real) * rho) (4 * rho + cError)

/-- A tube reference with an approximate common-`c` value lies in the
explicit sharp C2 ball. -/
theorem pairLocalTubeReference_mem_approxCommonC_c2Ball
    {radius : NNReal} (V globalCenter : Tube radius) (commonC : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho cError : Real)
    (hdistance : tubePairCoefficientDistance V globalCenter <= rho)
    (hcError : |tubeGraphC V - commonC| <= cError)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    InPointwiseC2BallOn (Icc A B)
      (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
        hfDeriv hf1Deriv A B hAB)
      (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB)
      (approximateCommonCLocalC2Radius rho cError) := by
  have hrho : 0 <= rho :=
    (tubePairCoefficientDistance_nonneg V globalCenter).trans hdistance
  have hcErrorNonneg : 0 <= cError :=
    (abs_nonneg (tubeGraphC V - commonC)).trans hcError
  intro z hz
  have h := pairLocalTubeReference_approxCommonC_jetBounds V globalCenter
    commonC f f1 f2 hfDeriv hf1Deriv A B hAB rho cError hdistance
      hcError hparameter hfunction hfirst hsecond z hz
  refine ⟨h.1.trans ?_, h.2.1.trans ?_, h.2.2.trans ?_⟩
  · exact (le_max_right _ _).trans' (by nlinarith)
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- Centering and then restricting a literal tube rectangle changes only
its base, so the same approximate-common-`c` C2 estimate survives exactly. -/
theorem exactLocal_centeredTube_mem_approxCommonC_c2Ball
    {radius : NNReal} (V globalCenter : Tube radius) (commonC : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B)
    (theta sourceDelta sourceScale delta localScale rho cError : Real)
    (hdistance : tubePairCoefficientDistance V globalCenter <= rho)
    (hcError : |tubeGraphC V - commonC| <= cError)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    InPointwiseC2BallOn (Icc A B)
      (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
        hfDeriv hf1Deriv A B hAB)
      (exactLocalC2GraphRectangle
        (centeredTubeC2GraphRectangle V f f1 f2 hfDeriv hf1Deriv
          theta sourceDelta sourceScale) delta localScale)
      (approximateCommonCLocalC2Radius rho cError) := by
  have hreference := pairLocalTubeReference_mem_approxCommonC_c2Ball
    V globalCenter commonC f f1 f2 hfDeriv hf1Deriv A B hAB rho cError
      hdistance hcError hparameter hfunction hfirst hsecond
  have hcentered : InPointwiseC2BallOn (Icc A B)
      (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
        hfDeriv hf1Deriv A B hAB)
      (centeredTubeC2GraphRectangle V f f1 f2 hfDeriv hf1Deriv
        theta sourceDelta sourceScale)
      (approximateCommonCLocalC2Radius rho cError) := by
    simpa only [pairLocalTubeReference, centeredTubeC2GraphRectangle,
      tubeC2GraphRectangle, InPointwiseC2BallOn] using hreference
  exact centeredC2GraphRectangleDilation_mem_c2BallOn hcentered

/-! ## A finite reduced-coefficient cover of source tubes -/

/-- The finite image of a source-tube map. -/
noncomputable def finiteTubeCoefficientCoverFamily
    {radius : NNReal} {item : Type u} [Fintype item]
    (sourceTube : item -> Tube radius) : Finset (Tube radius) := by
  classical
  exact Finset.univ.image sourceTube

/-- Every item gives a membership-bearing source tube in its finite image. -/
noncomputable def finiteTubeCoefficientCoverMember
    {radius : NNReal} {item : Type u} [Fintype item]
    (sourceTube : item -> Tube radius) (a : item) :
    FiniteMetricMember (finiteTubeCoefficientCoverFamily sourceTube) := by
  classical
  exact ⟨sourceTube a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩

/-- The canonical maximal-cover code of one source tube. -/
noncomputable def finiteTubeCoefficientCoverCode
    {radius : NNReal} {item : Type u} [Fintype item]
    (sourceTube : item -> Tube radius) (scale : Real) (a : item) :
    Tube radius := by
  classical
  exact finiteMetricCoverCode (finiteTubeCoefficientCoverFamily sourceTube)
    tubePairCoefficientDistance scale tubePairCoefficientDistance_comm
      (finiteTubeCoefficientCoverMember sourceTube a)

/-- At positive scale, every source tube is strictly within the scale of its
canonical finite-cover code. -/
theorem sourceTube_distance_coverCode_lt
    {radius : NNReal} {item : Type u} [Fintype item]
    (sourceTube : item -> Tube radius) (scale : Real) (hscale : 0 < scale)
    (a : item) :
    tubePairCoefficientDistance (sourceTube a)
      (finiteTubeCoefficientCoverCode sourceTube scale a) < scale := by
  classical
  have hself : forall V,
      V ∈ finiteTubeCoefficientCoverFamily sourceTube ->
        tubePairCoefficientDistance V V < scale := by
    intro V _hV
    simpa only [tubePairCoefficientDistance, coefficientDistance,
      tubePairDeltaA, tubePairDeltaB, tubePairDeltaD, sub_self, abs_zero,
      zero_add] using hscale
  exact distance_finiteMetricCoverCode_lt
    (finiteTubeCoefficientCoverFamily sourceTube)
    tubePairCoefficientDistance (scale := scale)
    tubePairCoefficientDistance_comm hself
      (finiteTubeCoefficientCoverMember sourceTube a)

/-- The approximate-common-C radius fits the Lemma 3.16 local radius once
the c-bucket error is at most 8 * ballRadius. -/
theorem approximateCommonCLocalC2Radius_le_twelve
    (ballRadius cError : Real) (hballRadius : 0 <= ballRadius)
    (hcError : cError <= 8 * ballRadius) :
    approximateCommonCLocalC2Radius ballRadius cError <=
      3 * (4 * ballRadius) := by
  rw [approximateCommonCLocalC2Radius, max_le_iff]
  constructor <;> nlinarith

/-- The existing paper three-shift smallness is much stronger than the
radius/2 <= 8*ballRadius inequality needed by the source-tube cover. -/
theorem radius_half_le_eight_ballRadius_of_threeShiftSmall
    {radius : NNReal} {globalDelta tGlobal ballRadius A B : Real}
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (B - A))
    (hthree : ActualY1PaperFineThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius)) :
    (radius : Real) / 2 <= 8 * ballRadius := by
  have scales :=
    actualY1PaperFineAutomaticThreeShiftNumerics_of_pairScaleSmall sharp hthree
  have hfactor := q_le_prop41TangencyScaleFactor_of_one_le scales.traceQ_one
  have hfactorOne : 1 <=
      prop41TangencyScaleFactor
        (actualY1PaperFineChoiceTraceQ
          (radius : Real) globalDelta tGlobal (4 * ballRadius)) :=
    scales.traceQ_one.trans hfactor
  have hsum : 10 <=
      10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            (radius : Real) globalDelta tGlobal (4 * ballRadius)) +
        actualY1PaperFineChoiceLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius) := by
    nlinarith [scales.lambda_pos]
  have hlarge : 1 <=
      46080 *
        (10 * prop41TangencyScaleFactor
            (actualY1PaperFineChoiceTraceQ
              (radius : Real) globalDelta tGlobal (4 * ballRadius)) +
          actualY1PaperFineChoiceLambda
            (radius : Real) globalDelta tGlobal (4 * ballRadius)) := by
    nlinarith
  have hradius : 0 <= (radius : Real) := NNReal.coe_nonneg radius
  have hsmall :
      46080 *
          (10 * prop41TangencyScaleFactor
              (actualY1PaperFineChoiceTraceQ
                (radius : Real) globalDelta tGlobal (4 * ballRadius)) +
            actualY1PaperFineChoiceLambda
              (radius : Real) globalDelta tGlobal (4 * ballRadius)) *
        (radius : Real) < 4 * ballRadius := by
    simpa only [ActualY1PaperFineThreeShiftPairScaleSmallness] using hthree
  have hradiusLt : (radius : Real) < 4 * ballRadius := by
    nlinarith
  nlinarith

#print axioms pairLocalTubeReference_approxCommonC_jetBounds
#print axioms pairLocalTubeReference_mem_approxCommonC_c2Ball
#print axioms exactLocal_centeredTube_mem_approxCommonC_c2Ball

end

end FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1
