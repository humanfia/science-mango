import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CommonReferenceScaleAuditV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41CommonReferenceIndependentScaleV1

open Set
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41CommonReferenceScaleAuditV1

noncomputable section

/-!
# Common reference with an independent Prop 4.1 scale

The C2-family radius used by the Prop 4.1 counting endpoint is kept separate
from the coefficient-separation scale of a retained pair.  No pair-separation
hypothesis occurs in this module.
-/

/-- Spend the strict sharp fixed-`c` reference margin against a uniform
absolute perturbation-weight envelope. -/
def fixedCommonCReferenceAutomaticTolerance
    (rho shiftEnvelope weightEnvelope prop41Scale : Real) : Real :=
  (3 * prop41Scale -
      max ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope)) /
    (weightEnvelope + 1)

theorem fixedCommonCReferenceAutomaticTolerance_pos
    {rho shiftEnvelope weightEnvelope prop41Scale : Real}
    (hweightEnvelope : 0 <= weightEnvelope)
    (hmargin : max ((401 / 100 : Real) * rho)
      (2 * rho + shiftEnvelope) < 3 * prop41Scale) :
    0 < fixedCommonCReferenceAutomaticTolerance
      rho shiftEnvelope weightEnvelope prop41Scale := by
  unfold fixedCommonCReferenceAutomaticTolerance
  apply div_pos (sub_pos.mpr hmargin)
  linarith

theorem fixedCommonCReferenceAutomaticTolerance_budget
    {rho shiftEnvelope weightEnvelope prop41Scale : Real}
    (hweightEnvelope : 0 <= weightEnvelope)
    (hmargin : max ((401 / 100 : Real) * rho)
      (2 * rho + shiftEnvelope) < 3 * prop41Scale) :
    max ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope) +
        fixedCommonCReferenceAutomaticTolerance
          rho shiftEnvelope weightEnvelope prop41Scale * weightEnvelope <=
      3 * prop41Scale := by
  let base := max ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope)
  have hdenominator : 0 < weightEnvelope + 1 := by linarith
  have hmarginNonneg : 0 <= 3 * prop41Scale - base := by
    dsimp [base]
    linarith
  have hfraction :
      ((3 * prop41Scale - base) / (weightEnvelope + 1)) * weightEnvelope <=
        3 * prop41Scale - base := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hdenominator).2
    exact mul_le_mul_of_nonneg_left (by linarith) hmarginNonneg
  unfold fixedCommonCReferenceAutomaticTolerance
  change base +
      ((3 * prop41Scale - base) / (weightEnvelope + 1)) * weightEnvelope <=
        3 * prop41Scale
  linarith

/-- The automatic tolerance controls an arbitrary base shift plus the small
general-position perturbation. -/
theorem fixedCommonC_combinedShift_budget
    {rho shiftEnvelope weightEnvelope prop41Scale baseShift weight epsilon : Real}
    (hweightEnvelope : 0 <= weightEnvelope)
    (hmargin : max ((401 / 100 : Real) * rho)
      (2 * rho + shiftEnvelope) < 3 * prop41Scale)
    (hbaseShift : |baseShift| <= shiftEnvelope)
    (hweight : |weight| <= weightEnvelope)
    (hepsilon : 0 < epsilon)
    (hepsilon_lt : epsilon < fixedCommonCReferenceAutomaticTolerance
      rho shiftEnvelope weightEnvelope prop41Scale) :
    max ((401 / 100 : Real) * rho)
        (2 * rho + |baseShift + epsilon * weight|) <=
      3 * prop41Scale := by
  let tolerance := fixedCommonCReferenceAutomaticTolerance
    rho shiftEnvelope weightEnvelope prop41Scale
  have htolerance : 0 < tolerance := by
    exact fixedCommonCReferenceAutomaticTolerance_pos
      hweightEnvelope hmargin
  have hproduct : epsilon * |weight| <= tolerance * weightEnvelope := by
    exact mul_le_mul hepsilon_lt.le hweight (abs_nonneg weight) htolerance.le
  have hshift : |baseShift + epsilon * weight| <=
      shiftEnvelope + tolerance * weightEnvelope := by
    calc
      |baseShift + epsilon * weight| <=
          |baseShift| + |epsilon * weight| := abs_add_le _ _
      _ = |baseShift| + epsilon * |weight| := by
        rw [abs_mul, abs_of_pos hepsilon]
      _ <= shiftEnvelope + tolerance * weightEnvelope :=
        add_le_add hbaseShift hproduct
  have htotal := fixedCommonCReferenceAutomaticTolerance_budget
    hweightEnvelope hmargin
  change max ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope) +
      tolerance * weightEnvelope <= 3 * prop41Scale at htotal
  apply max_le
  · calc
      (401 / 100 : Real) * rho <=
          max ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope) :=
        le_max_left _ _
      _ <= max ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope) +
          tolerance * weightEnvelope := by
        exact le_add_of_nonneg_right (mul_nonneg htolerance.le hweightEnvelope)
      _ <= 3 * prop41Scale := htotal
  · calc
      2 * rho + |baseShift + epsilon * weight| <=
          (2 * rho + shiftEnvelope) + tolerance * weightEnvelope := by
        linarith
      _ <= max ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope) +
          tolerance * weightEnvelope := by
        linarith [le_max_right ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope)]
      _ <= 3 * prop41Scale := htotal

/-- An explicit positive independent Prop 4.1 scale always exists for a
nonnegative reduced radius and base-shift envelope. -/
theorem exists_positive_prop41Scale_with_fixedCommonC_margin
    (rho shiftEnvelope : Real) (hrho : 0 <= rho)
    (hshiftEnvelope : 0 <= shiftEnvelope) :
    exists prop41Scale : Real, 0 < prop41Scale ∧
      max ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope) <
        3 * prop41Scale := by
  let base := max ((401 / 100 : Real) * rho) (2 * rho + shiftEnvelope)
  have hbase : 0 <= base := by
    dsimp [base]
    apply le_max_of_le_right
    nlinarith
  refine ⟨(base + 1) / 3, by positivity, ?_⟩
  dsimp [base]
  linarith

/-- A whole fixed-`c` family receives one positive perturbation tolerance
and one common synthetic reference at the independent `prop41Scale`.
Crucially, the statement has no `2 * prop41Scale` coefficient-separation
premise. -/
theorem exists_positive_tolerance_fixedCommonC_family_reference
    {alpha : Type*} [DecidableEq alpha] {radius : NNReal}
    (indices : Finset alpha) (T : alpha -> Tube radius)
    (baseShift weight : alpha -> Real)
    (globalCenter : Tube radius) (commonC : Real)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B)
    (rho shiftEnvelope weightEnvelope prop41Scale : Real)
    (hweightEnvelope : 0 <= weightEnvelope)
    (hmargin : max ((401 / 100 : Real) * rho)
      (2 * rho + shiftEnvelope) < 3 * prop41Scale)
    (hcommonC : forall i, i ∈ indices -> tubeGraphC (T i) = commonC)
    (hdistance : forall i, i ∈ indices ->
      tubePairCoefficientDistance (T i) globalCenter <= rho)
    (hbaseShift : forall i, i ∈ indices -> |baseShift i| <= shiftEnvelope)
    (hweight : forall i, i ∈ indices -> |weight i| <= weightEnvelope)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    exists externalTolerance : Real, 0 < externalTolerance ∧
      forall epsilon, 0 < epsilon -> epsilon < externalTolerance ->
        forall i, i ∈ indices ->
          InPointwiseC2BallOn (Icc A B)
            (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
              hfDeriv hf1Deriv A B hAB)
            (pairLocalTubeReference
              (traceTranslateTube (T i)
                (baseShift i + epsilon * weight i))
              f f1 f2 hfDeriv hf1Deriv A B hAB)
            (3 * prop41Scale) := by
  let externalTolerance := fixedCommonCReferenceAutomaticTolerance
    rho shiftEnvelope weightEnvelope prop41Scale
  refine ⟨externalTolerance,
    fixedCommonCReferenceAutomaticTolerance_pos
      hweightEnvelope hmargin, ?_⟩
  intro epsilon hepsilon hepsilon_lt i hi
  apply pairLocalTubeReference_traceTranslate_mem_fixedCommonC_three_pairScale
    (T i) globalCenter commonC (baseShift i + epsilon * weight i)
      f f1 f2 hfDeriv hf1Deriv A B hAB rho prop41Scale
      (hcommonC i hi) (hdistance i hi) hparameter hfunction hfirst hsecond
  exact fixedCommonC_combinedShift_budget hweightEnvelope hmargin
    (hbaseShift i hi) (hweight i hi) hepsilon hepsilon_lt

#print axioms fixedCommonCReferenceAutomaticTolerance
#print axioms fixedCommonCReferenceAutomaticTolerance_pos
#print axioms fixedCommonCReferenceAutomaticTolerance_budget
#print axioms fixedCommonC_combinedShift_budget
#print axioms exists_positive_prop41Scale_with_fixedCommonC_margin
#print axioms exists_positive_tolerance_fixedCommonC_family_reference

end

end FamilyStickyCinematicL32Prop41CommonReferenceIndependentScaleV1
