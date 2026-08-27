import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticReferenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1

open Set
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32TraceTangencyScaleUpperV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1

noncomputable section

/-!
# A sharp synthetic common-c reference

The reference below uses the global center's reduced `a`, `b`, and `d`
coefficients but replaces its irrelevant `c` coefficient by the exact common
slice value.  Thus every common-`c` tube is compared directly to the global
reduced-coefficient center, with no anchor-triangle loss.
-/

/-- The synthetic reference rectangle with the global center's reduced
coefficients and the retained family's exact common `c`. -/
def globalCenterFixedCommonCReference {radius : NNReal}
    (globalCenter : Tube radius) (commonC : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) : C2GraphRectangle where
  rectangle := {
    graph := cinematicTraceValue f
      (tubeGraphA globalCenter) (tubeGraphB globalCenter) commonC
        (tubeGraphD globalCenter)
    left := A
    right := B
    left_le_right := hAB
  }
  first := cinematicTraceFirstValue f f1
    (tubeGraphB globalCenter) commonC (tubeGraphD globalCenter)
  second := cinematicTraceSecondValue f1 f2
    (tubeGraphB globalCenter) (tubeGraphD globalCenter)
  graph_hasDeriv := fun z =>
    hasDerivAt_cinematicTraceValue f f1
      (tubeGraphA globalCenter) (tubeGraphB globalCenter) commonC
        (tubeGraphD globalCenter) z (hfDeriv z)
  first_hasDeriv := fun z =>
    hasDerivAt_cinematicTraceFirstValue f f1 f2
      (tubeGraphB globalCenter) commonC (tubeGraphD globalCenter) z
        (hfDeriv z) (hf1Deriv z)

/-- The sharp second-jet operator norm for the stated normalized analytic
bounds is `401/100`. -/
theorem abs_traceJet2_le_401_div_100_coefficientDistance
    (da db dd f1 f2 theta : Real)
    (htheta : |theta| <= 1) (hf1 : |f1| <= 2)
    (hf2 : |f2| <= 1 / 100) :
    |traceJet2 db dd f1 f2 theta| <=
      (401 / 100 : Real) * coefficientDistance da db dd := by
  have htwo : |2 * f1| <= 4 := by
    rw [abs_mul]
    norm_num
    linarith
  have hthetaF2 : |theta * f2| <= 1 / 100 := by
    rw [abs_mul]
    calc
      |theta| * |f2| <= 1 * |f2| :=
        mul_le_mul_of_nonneg_right htheta (abs_nonneg f2)
      _ <= 1 * (1 / 100 : Real) :=
        mul_le_mul_of_nonneg_left hf2 (by norm_num)
      _ = 1 / 100 := by ring
  have hinside : |2 * f1 + theta * f2| <= (401 / 100 : Real) := by
    calc
      |2 * f1 + theta * f2| <= |2 * f1| + |theta * f2| :=
        abs_add_le _ _
      _ <= 4 + (1 / 100 : Real) := add_le_add htwo hthetaF2
      _ = 401 / 100 := by ring
  have hlinear : |db * f2| <= (1 / 100 : Real) * |db| := by
    rw [abs_mul]
    calc
      |db| * |f2| <= |db| * (1 / 100 : Real) :=
        mul_le_mul_of_nonneg_left hf2 (abs_nonneg db)
      _ = (1 / 100 : Real) * |db| := by ring
  have hquadratic : |dd * (2 * f1 + theta * f2)| <=
      (401 / 100 : Real) * |dd| := by
    rw [abs_mul]
    calc
      |dd| * |2 * f1 + theta * f2| <=
          |dd| * (401 / 100 : Real) :=
        mul_le_mul_of_nonneg_left hinside (abs_nonneg dd)
      _ = (401 / 100 : Real) * |dd| := by ring
  calc
    |traceJet2 db dd f1 f2 theta| <=
        |db * f2| + |dd * (2 * f1 + theta * f2)| := by
      rw [traceJet2]
      exact abs_add_le _ _
    _ <= (1 / 100 : Real) * |db| +
        (401 / 100 : Real) * |dd| := add_le_add hlinear hquadratic
    _ <= (401 / 100 : Real) * coefficientDistance da db dd := by
      rw [coefficientDistance]
      nlinarith [abs_nonneg da, abs_nonneg db, abs_nonneg dd]

/-- Relative to the synthetic center, the value, first, and second jet
errors have respective constants `2`, `4`, and `401/100`. -/
theorem pairLocalTubeReference_fixedCommonC_jetBounds
    {radius : NNReal} (V globalCenter : Tube radius) (commonC : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho : Real)
    (hcommonC : tubeGraphC V = commonC)
    (hdistance : tubePairCoefficientDistance V globalCenter <= rho)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    forall z, z ∈ Icc A B ->
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).rectangle.graph z -
        (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).rectangle.graph z| <= 2 * rho ∧
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).first z -
        (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).first z| <= 4 * rho ∧
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).second z -
        (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).second z| <=
            (401 / 100 : Real) * rho := by
  intro z hz
  have hdistance' : coefficientDistance
      (tubePairDeltaA V globalCenter) (tubePairDeltaB V globalCenter)
        (tubePairDeltaD V globalCenter) <= rho := by
    simpa only [tubePairCoefficientDistance] using hdistance
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
              (tubePairDeltaD V globalCenter) (f z) z| := by
        simp only [pairLocalTubeReference, tubeC2GraphRectangle,
          globalCenterFixedCommonCReference]
        rw [hcommonC]
        simp only [cinematicTraceValue, traceJet0,
          tubePairDeltaA, tubePairDeltaB, tubePairDeltaD]
        congr 1
        ring
      _ <= 2 * coefficientDistance (tubePairDeltaA V globalCenter)
          (tubePairDeltaB V globalCenter)
            (tubePairDeltaD V globalCenter) := hvalueRaw
      _ <= 2 * rho := by linarith
  constructor
  · calc
      |(pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).first z -
          (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
            hfDeriv hf1Deriv A B hAB).first z| =
          |traceJet1 (tubePairDeltaB V globalCenter)
            (tubePairDeltaD V globalCenter) (f z) (f1 z) z| := by
        simp only [pairLocalTubeReference, tubeC2GraphRectangle,
          globalCenterFixedCommonCReference, tubeCinematicTraceFirstValue]
        rw [hcommonC]
        simp only [cinematicTraceFirstValue, traceJet1, tubePairDeltaB,
          tubePairDeltaD]
        congr 1
        ring
      _ <= 4 * coefficientDistance (tubePairDeltaA V globalCenter)
          (tubePairDeltaB V globalCenter)
            (tubePairDeltaD V globalCenter) := hfirstRaw
      _ <= 4 * rho := by linarith
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

/-- The resulting sharp common-`c` pointwise C2 radius is `401/100 * rho`.
The constant is governed by the second jet. -/
theorem pairLocalTubeReference_mem_globalCenterFixedCommonC_c2Ball
    {radius : NNReal} (V globalCenter : Tube radius) (commonC : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho : Real)
    (hcommonC : tubeGraphC V = commonC)
    (hdistance : tubePairCoefficientDistance V globalCenter <= rho)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    InPointwiseC2BallOn (Icc A B)
      (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
        hfDeriv hf1Deriv A B hAB)
      (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB)
      ((401 / 100 : Real) * rho) := by
  have hrho : 0 <= rho :=
    (tubePairCoefficientDistance_nonneg V globalCenter).trans hdistance
  intro z hz
  have h := pairLocalTubeReference_fixedCommonC_jetBounds V globalCenter
    commonC f f1 f2 hfDeriv hf1Deriv A B hAB rho hcommonC hdistance
      hparameter hfunction hfirst hsecond z hz
  exact ⟨h.1.trans (by nlinarith), h.2.1.trans (by nlinarith), h.2.2⟩

/-- The `401/100` coefficient is attained by concentrating all reduced
coefficient distance in `d` at the allowed endpoint jet values. -/
theorem common_c_secondJet_factor_401_div_100_attained
    (rho : Real) (hrho : 0 <= rho) :
    coefficientDistance 0 0 rho = rho ∧
      |traceJet2 0 rho 2 (1 / 100 : Real) 1| =
        (401 / 100 : Real) * rho := by
  constructor
  · simp only [coefficientDistance, abs_zero, zero_add, abs_of_nonneg hrho]
  · rw [traceJet2]
    have hnonneg : 0 <= 0 * (1 / 100 : Real) +
        rho * (2 * 2 + 1 * (1 / 100 : Real)) := by
      nlinarith
    rw [abs_of_nonneg hnonneg]
    ring

/-- At the available global coefficient radius, the sharp required C2
 radius cannot fit inside `3 * pairScale` under the stated scale direction. -/
theorem sharp_common_c_required_radius_not_le_three_pairScale
    (globalScale pairScale : Real) (hglobalScale : 0 < globalScale)
    (hpairScale : pairScale <= 3 * globalScale) :
    ¬ ((401 / 100 : Real) * (3 * globalScale) <= 3 * pairScale) := by
  intro hrequired
  nlinarith

/-- Consequently the available scale direction is insufficient: for
positive global scale and `pairScale <= 3 * globalScale`, the extremal tube
already has second-jet error strictly larger than `3 * pairScale`. -/
theorem sharp_common_c_radius_three_pairScale_obstruction
    (globalScale pairScale : Real) (hglobalScale : 0 < globalScale)
    (hpairScale : pairScale <= 3 * globalScale) :
    coefficientDistance 0 0 (3 * globalScale) = 3 * globalScale ∧
      3 * pairScale <
        |traceJet2 0 (3 * globalScale) 2 (1 / 100 : Real) 1| := by
  have hsharp := common_c_secondJet_factor_401_div_100_attained
    (3 * globalScale) (by positivity)
  refine ⟨hsharp.1, ?_⟩
  rw [hsharp.2]
  nlinarith

#print axioms globalCenterFixedCommonCReference
#print axioms abs_traceJet2_le_401_div_100_coefficientDistance
#print axioms pairLocalTubeReference_fixedCommonC_jetBounds
#print axioms pairLocalTubeReference_mem_globalCenterFixedCommonC_c2Ball
#print axioms common_c_secondJet_factor_401_div_100_attained
#print axioms sharp_common_c_required_radius_not_le_three_pairScale
#print axioms sharp_common_c_radius_three_pairScale_obstruction

end

end FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
