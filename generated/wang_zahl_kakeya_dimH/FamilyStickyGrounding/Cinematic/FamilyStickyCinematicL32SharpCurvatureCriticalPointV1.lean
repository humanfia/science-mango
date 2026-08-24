import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionHalfMarginV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32OscillationProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceCriticalPointV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceCriticalValueV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceTangencyMinimizerV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32SharpCurvatureCriticalPointV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32TraceCriticalPointV1
open FamilyStickyCinematicL32TraceCriticalValueV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionHalfMarginV1

/-!
# Critical point in the sharpened global-curvature branch

Provenance: PYZ Lemma 3.8(1a).  The tangency minimizer lies in the
concentric `J/2`; the primary-source normalization `|J| ~ 1` is represented
by the explicit lower width `1/2 <= |J|`.  Thus no short-interval or fixed
buffer premise is needed.
-/

/-- A small attained tangency parameter in the globally curvature-separated
Wang--Zahl branch produces a true critical point on `J`, whose critical value
is at most ten times the attained tangency parameter. -/
theorem trace_sharp_curvature_small_tangency_exists_criticalPoint_value_bound
    (f f1 f2 : Real -> Real) (da db dd Delta thetaDelta : Real)
    {A B : Real}
    (hwidth : (1 / 2 : Real) <= B - A)
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hthetaDelta :
      thetaDelta ∈ centeredFractionIcc A B (1 / 2 : Real))
    (hDeltaDef :
      Delta = traceTangencyCost f f1 da db dd thetaDelta)
    (hDeltaSmall : Delta < coefficientDistance da db dd / 1200)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hcurvatureStrict : forall z, z ∈ Icc A B ->
      coefficientDistance da db dd / 45 <
        |traceSecondDerivative f1 f2 db dd z|) :
    ∃ theta0, theta0 ∈ Icc A B ∧
      traceFirstDerivative f f1 db dd theta0 = 0 ∧
      |traceFunction f da db dd theta0| <= 10 * Delta := by
  let coefficient := coefficientDistance da db dd
  let kappa := coefficient / 45
  have hcoefficientPos : 0 < coefficient := by
    simpa [coefficient] using hcoefficient
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    positivity
  have hAB : A <= B := by linarith
  have hhalfSubset : centeredFractionIcc A B (1 / 2 : Real) ⊆ Icc A B := by
    intro z hz
    rcases hz with ⟨hzLeft, hzRight⟩
    constructor <;>
      simp only [centeredFractionLeft,
        centeredFractionRight] at * <;>
      linarith
  have hthetaOuter : thetaDelta ∈ Icc A B :=
    hhalfSubset hthetaDelta
  have hDelta : 0 <= Delta := by
    rw [hDeltaDef, traceTangencyCost]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hanchorValue : |traceFunction f da db dd thetaDelta| <= Delta := by
    rw [hDeltaDef, traceTangencyCost]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hanchorSlope :
      |traceFirstDerivative f f1 db dd thetaDelta| <= Delta := by
    rw [hDeltaDef, traceTangencyCost]
    exact le_add_of_nonneg_left (abs_nonneg _)
  have hmargins := mem_half_has_eighth_whole_margin hwidth hthetaDelta
  have hDeltaEighth : Delta <= kappa * (1 / 8 : Real) := by
    dsimp [kappa, coefficient]
    nlinarith
  have hleftBuffer : Delta <= kappa * (thetaDelta - A) :=
    hDeltaEighth.trans
      (mul_le_mul_of_nonneg_left hmargins.1 hkappa.le)
  have hrightBuffer : Delta <= kappa * (B - thetaDelta) :=
    hDeltaEighth.trans
      (mul_le_mul_of_nonneg_left hmargins.2 hkappa.le)
  have hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |traceSecondDerivative f1 f2 db dd z| := by
    intro z hz
    exact le_of_lt (by
      simpa [kappa, coefficient] using hcurvatureStrict z hz)
  obtain ⟨theta0, htheta0Critical, _hunique⟩ :=
    trace_buffered_anchor_existsUnique_criticalPoint
      f f1 f2 db dd hthetaOuter hkappa hfDeriv hf1Deriv hf2Continuous
      hcurvatureLower hanchorSlope hleftBuffer hrightBuffer
  have hcurvatureUpper : forall z, z ∈ Icc A B ->
      |traceSecondDerivative f1 f2 db dd z| <= 5 * coefficient := by
    intro z hz
    simpa [traceSecondDerivative, coefficient] using
      abs_traceJet2_le_five_coefficientDistance
        da db dd (f1 z) (f2 z) z
        (hparameter z hz) (hf1Upper z hz) (hf2 z hz)
  have hvalue := trace_criticalPoint_value_le_anchorValue_add_quadratic_error
    f f1 f2 da db dd htheta0Critical.1 hthetaOuter
    (show 0 <= 5 * coefficient by positivity) hkappa
    htheta0Critical.2 hfDeriv hf1Deriv hf2Continuous hcurvatureUpper
    hcurvatureLower hanchorValue hanchorSlope
  have hscaled : 1200 * Delta ^ 2 <= Delta * coefficient := by
    have hsmall : Delta < coefficient / 1200 := by
      simpa [coefficient] using hDeltaSmall
    have hmul := mul_le_mul_of_nonneg_left hsmall.le hDelta
    nlinarith
  have herrorIdentity :
      (5 * coefficient) * (Delta / kappa) ^ 2 =
        10125 * Delta ^ 2 / coefficient := by
    dsimp [kappa]
    field_simp [ne_of_gt hcoefficientPos]
    ring
  have herror :
      (5 * coefficient) * (Delta / kappa) ^ 2 <= 9 * Delta := by
    rw [herrorIdentity]
    apply (div_le_iff₀ hcoefficientPos).2
    nlinarith [sq_nonneg Delta]
  refine ⟨theta0, htheta0Critical.1, htheta0Critical.2, ?_⟩
  exact hvalue.trans (by nlinarith)

#print axioms trace_sharp_curvature_small_tangency_exists_criticalPoint_value_bound

end FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
