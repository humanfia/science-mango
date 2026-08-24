import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionNestingV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceEasyRectangleTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceMediumRectangleTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceHardTangencyProductV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TangencyIntervalSeparationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceCriticalDerivativeGrowthV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceTangencyScaleUpperV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32CanonicalQuarterTangencyProductV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
open FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
open FamilyStickyCinematicL32TraceEasyRectangleTangencyV1
open FamilyStickyCinematicL32TraceMediumRectangleTangencyV1
open FamilyStickyCinematicL32TraceHardTangencyProductV1
open FamilyStickyCinematicL32TangencyIntervalSeparationV1
open FamilyStickyCinematicL32TraceCriticalDerivativeGrowthV1
open FamilyStickyCinematicL32TraceTangencyScaleUpperV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1

/-!
# Faithful tangency product on `J/4` from the canonical `J/2` minimum

This is the interval geometry of PYZ Lemmas 3.8--3.9.  The proof internally
handles the large-minimum, globally first-jet, medium-curvature, and hard-
curvature branches.  In the hard branch, a critical point outside `J/2` is
uniformly separated from `J/4`; if it lies inside, minimality supplies the
critical-value lower bound.
-/

/-- Every connected trace-sublevel interval in `J/4` obeys a uniform
tangency product.  The deliberately generous numerical constant keeps all
five produced analytic branches under one exact conclusion. -/
theorem canonical_quarter_rectangle_width_forces_tangency_product
    (f f1 f2 : Real -> Real)
    (da db dd Delta thetaDelta : Real)
    {A B x y delta rho : Real}
    (hxy : x <= y)
    (hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hwidth : (1 / 2 : Real) <= B - A)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hdeltaSmall : delta < coefficientDistance da db dd / 2400)
    (hthetaDelta :
      thetaDelta ∈ centeredFractionIcc A B (1 / 2 : Real))
    (hDeltaDef : Delta = traceTangencyCost f f1 da db dd thetaDelta)
    (hminimum : forall z,
      z ∈ centeredFractionIcc A B (1 / 2 : Real) ->
        Delta <= traceTangencyCost f f1 da db dd z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcomponentSublevel : forall z, z ∈ Icc x y ->
      |traceFunction f da db dd z| <= delta)
    (hrectangleWidth : Real.sqrt (delta / rho) <= y - x) :
    (1 / 3600000 : Real) ^ 2 * (Delta + delta) *
        coefficientDistance da db dd <=
      20000 * delta * rho := by
  let coefficient := coefficientDistance da db dd
  let a : Real := 1 / 3600000
  let halfA := centeredFractionLeft A B (1 / 2 : Real)
  let halfB := centeredFractionRight A B (1 / 2 : Real)
  let baseA := centeredFractionLeft A B (1 / 4 : Real)
  let baseB := centeredFractionRight A B (1 / 4 : Real)
  have hAB : A <= B := by linarith
  have hhalfWhole := half_subset_whole hAB
  have hbaseHalf := quarter_subset_half hAB
  have hbaseWhole := quarter_subset_whole hAB
  have hthetaOuter : thetaDelta ∈ Icc A B :=
    hhalfWhole hthetaDelta
  have hxOuter : x ∈ Icc A B := hbaseWhole hxBase
  have hyOuter : y ∈ Icc A B := hbaseWhole hyBase
  have hcomponentBase : Icc x y ⊆
      centeredFractionIcc A B (1 / 4 : Real) :=
    Icc_subset_Icc hxBase.1 hyBase.2
  have hcomponentOuter : Icc x y ⊆ Icc A B :=
    Icc_subset_Icc hxOuter.1 hyOuter.2
  have hcomponentHalf : Icc x y ⊆
      centeredFractionIcc A B (1 / 2 : Real) :=
    hcomponentBase.trans hbaseHalf
  have hDelta : 0 <= Delta := by
    rw [hDeltaDef, traceTangencyCost]
    positivity
  have hcoefficientNonneg : 0 <= coefficient := by
    simpa [coefficient] using hcoefficient.le
  have hDeltaUpper : Delta <= 6 * coefficient := by
    exact attained_traceTangencyParameter_le_six_coefficientDistance
      f f1 da db dd Delta thetaDelta hDeltaDef
      (hparameter thetaDelta hthetaOuter)
      (hft thetaDelta hthetaOuter)
      (hf1Upper thetaDelta hthetaOuter)
  have hsumScale : Delta + delta <= 7 * coefficient := by
    dsimp [coefficient] at *
    nlinarith
  have haPos : 0 < a := by norm_num [a]
  have haLeTwelfth : a <= (1 / 12 : Real) := by norm_num [a]
  have haLeFortyFive : a <= (1 / 45 : Real) := by norm_num [a]
  have haSqLeFortyFive : a ^ 2 <= (1 / 45 : Real) := by
    norm_num [a]
  have hderivComponent : forall z, z ∈ Icc x y ->
      HasDerivAt f (f1 z) z :=
    fun z hz => hfDeriv z (hcomponentOuter hz)
  have hderiv1Component : forall z, z ∈ Icc x y ->
      HasDerivAt f1 (f2 z) z :=
    fun z hz => hf1Deriv z (hcomponentOuter hz)
  have easyFromFirstLower : forall m : Real,
      0 < m -> a * coefficient <= m ->
      (forall z, z ∈ Icc x y ->
        m <= |traceFirstDerivative f f1 db dd z|) ->
      a ^ 2 * (Delta + delta) * coefficient <=
        20000 * delta * rho := by
    intro m hm hscale hfirstLower
    have heasy := trace_easy_rectangle_width_forces_tangency_product
      f f1 f2 da db dd hxy
      (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy)
      hdelta hrho hm haPos hcoefficient (by norm_num : (0 : Real) <= 7)
      hsumScale hscale hderivComponent hderiv1Component
      hfirstLower hcomponentSublevel hrectangleWidth
    simpa only [a, coefficient] using
      heasy.trans (by
        have : 0 <= delta * rho := by positivity
        nlinarith)
  by_cases hDeltaSmall : Delta < coefficient / 1200
  · rcases global_value_or_first_or_second_jet_separation_sharp da db dd with
        hvalue | hfirst | hcurvature
    · have hxSub := hcomponentSublevel x (left_mem_Icc.2 hxy)
      have hxLarge := hvalue (f x) x
        (hparameter x hxOuter) (hft x hxOuter)
      have hxLarge' : coefficient / 3 <=
          |traceFunction f da db dd x| := by
        simpa [coefficient, traceFunction] using hxLarge
      exfalso
      dsimp [coefficient] at *
      nlinarith
    · apply easyFromFirstLower (coefficient / 12)
      · positivity
      · simpa [div_eq_mul_inv, mul_comm] using
          (mul_le_mul_of_nonneg_right haLeTwelfth hcoefficientNonneg)
      · intro z hz
        simpa [coefficient, traceFirstDerivative] using
          hfirst (f z) (f1 z) z
            (hparameter z (hcomponentOuter hz))
            (hft z (hcomponentOuter hz))
            (hf1Lower z (hcomponentOuter hz))
            (hf1Upper z (hcomponentOuter hz))
    · have hcurvatureStrict : forall z, z ∈ Icc A B ->
          coefficient / 45 <
            |traceSecondDerivative f1 f2 db dd z| := by
        intro z hz
        simpa [coefficient, traceSecondDerivative] using
          hcurvature (f1 z) (f2 z) z (hparameter z hz)
            (hf1Lower z hz) (hf2 z hz)
      have hcurvatureLower : forall z, z ∈ Icc A B ->
          coefficient / 45 <=
            |traceSecondDerivative f1 f2 db dd z| :=
        fun z hz => le_of_lt (hcurvatureStrict z hz)
      have hcurvatureUpper : forall z, z ∈ Icc A B ->
          |traceSecondDerivative f1 f2 db dd z| <= 5 * coefficient := by
        intro z hz
        simpa [coefficient, traceSecondDerivative] using
          FamilyStickyCinematicL32OscillationProducerV1.abs_traceJet2_le_five_coefficientDistance
            da db dd (f1 z) (f2 z) z (hparameter z hz)
            (hf1Upper z hz) (hf2 z hz)
      obtain ⟨theta0, htheta0, hcritical, hcriticalValue⟩ :=
        trace_sharp_curvature_small_tangency_exists_criticalPoint_value_bound
          f f1 f2 da db dd Delta thetaDelta hwidth
          (by simpa [coefficient] using hcoefficient) hthetaDelta hDeltaDef
          (by simpa [coefficient] using hDeltaSmall)
          hfDeriv hf1Deriv hf2Continuous hparameter hf1Upper hf2
          (by simpa [coefficient] using hcurvatureStrict)
      by_cases hmedium : Delta <= 3 * delta
      · have hmediumRaw :=
          trace_medium_rectangle_width_forces_tangency_product
            f f1 f2 da db dd hxy htheta0 hxOuter hyOuter
            hdelta hrho (show 0 < coefficient / 45 by positivity)
            (show 0 < a ^ 2 by positivity) hcoefficient
            (show 0 <= (30 : Real) by norm_num)
            (show 10 * Delta <= 30 * delta by nlinarith)
            (show a ^ 2 * coefficient <= coefficient / 45 by
              simpa [div_eq_mul_inv, mul_comm] using
                (mul_le_mul_of_nonneg_right haSqLeFortyFive
                  hcoefficientNonneg))
            hcritical hfDeriv hf1Deriv hf2Continuous hcurvatureLower
            hcriticalValue
            (hcomponentSublevel x (left_mem_Icc.2 hxy))
            (hcomponentSublevel y (right_mem_Icc.2 hxy))
            hrectangleWidth
        have hsumLe : Delta + delta <= 10 * Delta + delta := by
          nlinarith
        have hfactor : a ^ 2 * (Delta + delta) * coefficient <=
            a ^ 2 * (10 * Delta + delta) * coefficient := by
          have hac : 0 <= a ^ 2 * coefficient := by positivity
          nlinarith
        exact hfactor.trans (hmediumRaw.trans (by
          have : 0 <= delta * rho := by positivity
          norm_num
          nlinarith))
      · have hhard : 3 * delta <= Delta := le_of_not_ge hmedium
        have hgap : (B - A) / 8 <=
            centeredFractionLeft A B (1 / 4 : Real) -
              centeredFractionLeft A B (1 / 2 : Real) := by
          simp only [centeredFractionLeft]
          ring_nf
          exact le_rfl
        have hgapRight :
            centeredFractionRight A B (1 / 4 : Real) +
                (B - A) / 8 <=
              centeredFractionRight A B (1 / 2 : Real) := by
          simp only [centeredFractionRight]
          ring_nf
          exact le_rfl
        rcases critical_mem_minimizerInterval_or_base_separated
            (minA := centeredFractionLeft A B (1 / 2 : Real))
            (minB := centeredFractionRight A B (1 / 2 : Real))
            (baseA := centeredFractionLeft A B (1 / 4 : Real))
            (baseB := centeredFractionRight A B (1 / 4 : Real))
            (theta0 := theta0) (s := (B - A) / 8)
            (by linarith [hgap]) hgapRight with hcriticalInside | hbaseFar
        · have hcenter : Delta <= |traceFunction f da db dd theta0| := by
            have hmin := hminimum theta0 hcriticalInside
            simpa [traceTangencyCost, hcritical] using hmin
          have hhardRaw := trace_hard_rectangle_width_forces_tangency_product
            f f1 f2 da db dd hxy htheta0 hxOuter hyOuter hdelta hrho
            (show 0 < 5 * coefficient by positivity)
            (show 0 < coefficient / 45 by positivity)
            hcoefficient haPos hhard
            (show a * coefficient <= coefficient / 45 by
              simpa [div_eq_mul_inv, mul_comm] using
                (mul_le_mul_of_nonneg_right haLeFortyFive
                  hcoefficientNonneg))
            (show 5 * coefficient <= 5 * coefficient by rfl)
            hcritical hfDeriv hf1Deriv hf2Continuous hcurvatureUpper
            hcurvatureLower hcenter hcomponentSublevel hrectangleWidth
          simpa only [a, coefficient] using
            hhardRaw.trans (by
              have : 0 <= delta * rho := by positivity
              nlinarith)
        · let m := (coefficient / 45) * ((B - A) / 8)
          have hgapPos : 0 < (B - A) / 8 := by positivity
          have hm : 0 < m := by
            dsimp [m]
            positivity
          have hscale : a * coefficient <= m := by
            have hgapLower : (1 / 16 : Real) <= (B - A) / 8 := by
              nlinarith
            have hraw : coefficient / 720 <= m := by
              dsimp [m]
              have := mul_le_mul_of_nonneg_left hgapLower
                (show 0 <= coefficient / 45 by positivity)
              nlinarith
            have ha720 : a <= (1 / 720 : Real) := by norm_num [a]
            exact (mul_le_mul_of_nonneg_right ha720
              hcoefficientNonneg).trans
              (by simpa [div_eq_mul_inv, mul_comm] using hraw)
          apply easyFromFirstLower m hm hscale
          intro z hz
          have hgrowth := trace_curvature_lower_forces_firstDerivative_growth
            f f1 f2 db dd htheta0 (hcomponentOuter hz)
            (show 0 < coefficient / 45 by positivity) hcritical
            hfDeriv hf1Deriv hf2Continuous hcurvatureLower
          calc
            m <= (coefficient / 45) * |z - theta0| := by
              exact mul_le_mul_of_nonneg_left
                (hbaseFar z (hcomponentBase hz))
                (show 0 <= coefficient / 45 by positivity)
            _ <= |traceFirstDerivative f f1 db dd z| := hgrowth
  · let m := Delta - delta
    have hDeltaLarge : coefficient / 1200 <= Delta :=
      le_of_not_gt hDeltaSmall
    have hm : 0 < m := by
      dsimp [m]
      nlinarith
    have hscale : a * coefficient <= m := by
      have ha2400 : a <= (1 / 2400 : Real) := by norm_num [a]
      have hraw : coefficient / 2400 <= Delta - delta := by
        nlinarith
      exact (mul_le_mul_of_nonneg_right ha2400
        hcoefficientNonneg).trans
        (by simpa [div_eq_mul_inv, mul_comm, m] using hraw)
    apply easyFromFirstLower m hm hscale
    intro z hz
    have hlower := hminimum z (hcomponentHalf hz)
    rw [traceTangencyCost] at hlower
    have hsublevel := hcomponentSublevel z hz
    dsimp [m]
    linarith

#print axioms canonical_quarter_rectangle_width_forces_tangency_product

end FamilyStickyCinematicL32CanonicalQuarterTangencyProductV1
