import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41CommonReferenceScaleAuditV1

open Set
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1

noncomputable section

/-!
# Common-reference scale audit

This module records the exact scalar interface supplied by a synthetic
fixed-`c` center, including a constant trace translation, and the scale
obstruction forced by the existing global-norm ball and pair separation.
-/

/-- A pair separated by `2 * pairScale` inside the same reduced-coefficient
`3 * globalScale` ball necessarily has `pairScale <= 3 * globalScale`. -/
theorem pairScale_le_three_mul_globalScale_of_twoSeparated_in_globalBall
    {radius : NNReal} (T U globalCenter : Tube radius)
    (globalScale pairScale : Real)
    (hT : tubePairCoefficientDistance T globalCenter <= 3 * globalScale)
    (hU : tubePairCoefficientDistance U globalCenter <= 3 * globalScale)
    (hseparated : 2 * pairScale <= tubePairCoefficientDistance T U) :
    pairScale <= 3 * globalScale := by
  have hupper : tubePairCoefficientDistance T U <= 6 * globalScale :=
    tubePairCoefficientDistance_le_six_mul_of_common_center
      T U globalCenter hT hU
  linarith

/-- The sharp fixed-`c` reference radius after translating only the `a`
coefficient is the maximum of the second-jet budget and the translated
value-jet budget.  This improves the old additive `5 * rho + |s|` radius
without hiding the translation in coefficient distance. -/
theorem pairLocalTubeReference_traceTranslate_mem_globalCenterFixedCommonC_c2Ball
    {radius : NNReal} (T globalCenter : Tube radius) (commonC s : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho : Real)
    (hcommonC : tubeGraphC T = commonC)
    (hdistance : tubePairCoefficientDistance T globalCenter <= rho)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    InPointwiseC2BallOn (Icc A B)
      (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
        hfDeriv hf1Deriv A B hAB)
      (pairLocalTubeReference (traceTranslateTube T s)
        f f1 f2 hfDeriv hf1Deriv A B hAB)
      (max ((401 / 100 : Real) * rho) (2 * rho + |s|)) := by
  have hbase := pairLocalTubeReference_fixedCommonC_jetBounds
    T globalCenter commonC f f1 f2 hfDeriv hf1Deriv A B hAB rho
      hcommonC hdistance hparameter hfunction hfirst hsecond
  intro z hz
  have hdata := hbase z hz
  constructor
  · change |cinematicTraceValue f
        (tubeGraphA (traceTranslateTube T s))
        (tubeGraphB (traceTranslateTube T s))
        (tubeGraphC (traceTranslateTube T s))
        (tubeGraphD (traceTranslateTube T s)) z -
      (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
        hfDeriv hf1Deriv A B hAB).rectangle.graph z| <= _
    rw [cinematicTraceValue_traceTranslateTube]
    calc
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z + s -
        (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
          hfDeriv hf1Deriv A B hAB).rectangle.graph z| =
          |(cinematicTraceValue f
              (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
            (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
              hfDeriv hf1Deriv A B hAB).rectangle.graph z) + s| := by ring_nf
      _ <= |cinematicTraceValue f
              (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
            (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
              hfDeriv hf1Deriv A B hAB).rectangle.graph z| + |s| :=
        abs_add_le _ _
      _ <= 2 * rho + |s| := add_le_add hdata.1 le_rfl
      _ <= max ((401 / 100 : Real) * rho) (2 * rho + |s|) :=
        le_max_right _ _
  constructor
  · have hle : 4 * rho <=
        max ((401 / 100 : Real) * rho) (2 * rho + |s|) := by
      have hrho : 0 <= rho :=
        (tubePairCoefficientDistance_nonneg T globalCenter).trans hdistance
      exact (by nlinarith : 4 * rho <= (401 / 100 : Real) * rho) |>.trans
        (le_max_left _ _)
    have := hdata.2.1.trans hle
    simpa only [pairLocalTubeReference, tubeC2GraphRectangle,
      tubeCinematicTraceFirstValue, cinematicTraceFirstValue,
      tubeGraphB_traceTranslateTube, tubeGraphC_traceTranslateTube,
      tubeGraphD_traceTranslateTube] using this
  · have hle := le_max_left ((401 / 100 : Real) * rho) (2 * rho + |s|)
    have := hdata.2.2.trans hle
    simpa only [pairLocalTubeReference, tubeC2GraphRectangle,
      tubeCinematicTraceSecondValue, cinematicTraceSecondValue,
      tubeGraphB_traceTranslateTube, tubeGraphD_traceTranslateTube] using this

/-- The exact scalar budget that fills the existing endpoint's literal
`3 * pairScale` common-reference field. -/
theorem pairLocalTubeReference_traceTranslate_mem_fixedCommonC_three_pairScale
    {radius : NNReal} (T globalCenter : Tube radius) (commonC s : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (rho pairScale : Real)
    (hcommonC : tubeGraphC T = commonC)
    (hdistance : tubePairCoefficientDistance T globalCenter <= rho)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hbudget : max ((401 / 100 : Real) * rho) (2 * rho + |s|) <=
      3 * pairScale) :
    InPointwiseC2BallOn (Icc A B)
      (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
        hfDeriv hf1Deriv A B hAB)
      (pairLocalTubeReference (traceTranslateTube T s)
        f f1 f2 hfDeriv hf1Deriv A B hAB)
      (3 * pairScale) := by
  have hreference :=
    pairLocalTubeReference_traceTranslate_mem_globalCenterFixedCommonC_c2Ball
      T globalCenter commonC s f f1 f2 hfDeriv hf1Deriv A B hAB rho
        hcommonC hdistance hparameter hfunction hfirst hsecond
  intro z hz
  have h := hreference z hz
  exact ⟨h.1.trans hbudget, h.2.1.trans hbudget, h.2.2.trans hbudget⟩

/-- The fixed-`c` translated budget is exactly two scalar inequalities: the
sharp second-jet radius and the translated value-jet radius. -/
theorem fixedCommonC_traceTranslate_budget_iff
    (rho s pairScale : Real) :
    max ((401 / 100 : Real) * rho) (2 * rho + |s|) <= 3 * pairScale <->
      (401 / 100 : Real) * rho <= 3 * pairScale ∧
        2 * rho + |s| <= 3 * pairScale := by
  exact max_le_iff

/-- In particular, any scalar-only producer must localize the reduced
coefficient radius to at most `300/401 * pairScale`. -/
theorem reducedCoefficientRadius_le_300_div_401_pairScale_of_budget
    (rho s pairScale : Real)
    (hbudget : max ((401 / 100 : Real) * rho) (2 * rho + |s|) <=
      3 * pairScale) :
    rho <= (300 / 401 : Real) * pairScale := by
  have hsecond := (fixedCommonC_traceTranslate_budget_iff
    rho s pairScale).mp hbudget |>.1
  nlinarith

/-- The global-ball/separation inputs force exactly the scale direction that
contradicts the sharp fixed-`c` common-reference budget. -/
theorem sharp_fixedCommonC_reference_budget_obstruction_of_globalBall
    {radius : NNReal} (T U globalCenter : Tube radius)
    (globalScale pairScale : Real) (hglobalScale : 0 < globalScale)
    (hT : tubePairCoefficientDistance T globalCenter <= 3 * globalScale)
    (hU : tubePairCoefficientDistance U globalCenter <= 3 * globalScale)
    (hseparated : 2 * pairScale <= tubePairCoefficientDistance T U) :
    ¬ ((401 / 100 : Real) * (3 * globalScale) <= 3 * pairScale) := by
  exact sharp_common_c_required_radius_not_le_three_pairScale
    globalScale pairScale hglobalScale
      (pairScale_le_three_mul_globalScale_of_twoSeparated_in_globalBall
        T U globalCenter globalScale pairScale hT hU hseparated)

/-- Adding a constant trace translation cannot repair the sharp global-ball
obstruction: its cost occurs in the other branch of the maximum. -/
theorem sharp_fixedCommonC_perturbed_budget_obstruction_of_globalBall
    {radius : NNReal} (T U globalCenter : Tube radius)
    (globalScale pairScale s : Real) (hglobalScale : 0 < globalScale)
    (hT : tubePairCoefficientDistance T globalCenter <= 3 * globalScale)
    (hU : tubePairCoefficientDistance U globalCenter <= 3 * globalScale)
    (hseparated : 2 * pairScale <= tubePairCoefficientDistance T U) :
    ¬ (max ((401 / 100 : Real) * (3 * globalScale))
      (2 * (3 * globalScale) + |s|) <= 3 * pairScale) := by
  intro hbudget
  exact sharp_fixedCommonC_reference_budget_obstruction_of_globalBall
    T U globalCenter globalScale pairScale hglobalScale hT hU hseparated
      ((fixedCommonC_traceTranslate_budget_iff
        (3 * globalScale) s pairScale).mp hbudget).1

#print axioms fixedCommonC_traceTranslate_budget_iff
#print axioms reducedCoefficientRadius_le_300_div_401_pairScale_of_budget
#print axioms sharp_fixedCommonC_perturbed_budget_obstruction_of_globalBall

#print axioms pairScale_le_three_mul_globalScale_of_twoSeparated_in_globalBall
#print axioms pairLocalTubeReference_traceTranslate_mem_globalCenterFixedCommonC_c2Ball
#print axioms pairLocalTubeReference_traceTranslate_mem_fixedCommonC_three_pairScale
#print axioms sharp_fixedCommonC_reference_budget_obstruction_of_globalBall

end

end FamilyStickyCinematicL32Prop41CommonReferenceScaleAuditV1
