import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvatureRootEncCardV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualOppositeEndpointRootEncCardV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairTraceV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32GlobalTraceRootEncCardCleanV2

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvatureRootEncCardV1
open FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32Prop41ActualOppositeEndpointRootEncCardV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-! A global coefficient regime replaces the incompatible short-interval
assumption in the old actual boundary-overlap chain. -/

theorem traceFunction_rootSet_encard_le_two_global
    (f f1 f2 : Real -> Real) (da db dd : Real) {A B : Real}
    (hAB : A <= B)
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) :
    {z | z ∈ Icc A B ∧ traceFunction f da db dd z = 0}.encard <= 2 := by
  have htraceDeriv : forall z, z ∈ Icc A B ->
      HasDerivAt (traceFunction f da db dd)
        (traceFirstDerivative f f1 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFunction f f1 da db dd z (hfDeriv z hz)
  have hfirstDeriv : forall z, z ∈ Icc A B ->
      HasDerivAt (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFirstDerivative f f1 f2 db dd z
      (hfDeriv z hz) (hf1Deriv z hz)
  rcases global_value_or_first_or_second_jet_separation_sharp da db dd with
      hvalue | hfirst | hsecond
  · have hempty :
        {z | z ∈ Icc A B ∧ traceFunction f da db dd z = 0} = ∅ := by
      ext z
      constructor
      · rintro ⟨hz, hzero⟩
        have hlarge : coefficientDistance da db dd / 3 <=
            |traceFunction f da db dd z| := by
          simpa [traceFunction] using
            hvalue (f z) z (hparameter z hz) (hft z hz)
        rw [hzero, abs_zero] at hlarge
        nlinarith
      · simp
    rw [hempty]
    norm_num
  · have hkappa : 0 < coefficientDistance da db dd / 12 := by
      positivity
    have hone := absFirstDerivative_rootSet_encard_le_one
      (traceFunction f da db dd) (traceFirstDerivative f f1 db dd)
      hAB hkappa htraceDeriv (HasDerivAt.continuousOn hfirstDeriv)
      (fun z hz => by
        simpa [traceFirstDerivative] using
          hfirst (f z) (f1 z) z (hparameter z hz) (hft z hz)
            (hf1Lower z hz) (hf1Upper z hz))
    exact hone.trans (by norm_num)
  · have hkappa : 0 < coefficientDistance da db dd / 45 := by
      positivity
    exact rootSet_encard_le_two_of_abs_secondDerivative_lower
      (traceFunction f da db dd) (traceFirstDerivative f f1 db dd)
      (traceSecondDerivative f1 f2 db dd) hkappa htraceDeriv hfirstDeriv
      (fun z hz => le_of_lt (by
        simpa [traceSecondDerivative] using
          hsecond (f1 z) (f2 z) z (hparameter z hz)
            (hf1Lower z hz) (hf2 z hz)))

theorem tubeCinematicTrace_pair_rootSet_encard_le_two_global
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) {A B : Real}
    (hAB : A <= B) (hcommonC : tubeGraphC T = tubeGraphC U)
    (hcoefficient : 0 < tubePairCoefficientDistance T U)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) :
    {z | z ∈ Icc A B ∧
      cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T) z =
        cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U) z}.encard <= 2 := by
  have hroots :
      {z | z ∈ Icc A B ∧
        cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
            (tubeGraphC T) (tubeGraphD T) z =
          cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
            (tubeGraphC U) (tubeGraphD U) z} =
      {z | z ∈ Icc A B ∧
        traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) z = 0} := by
    ext z
    constructor
    · rintro ⟨hz, heq⟩
      refine ⟨hz, ?_⟩
      rw [← tube_cinematicTraceValue_sub_eq_traceFunction T U f hcommonC,
        heq, sub_self]
    · rintro ⟨hz, hzero⟩
      refine ⟨hz, ?_⟩
      have hsub := tube_cinematicTraceValue_sub_eq_traceFunction
        T U f hcommonC z
      rw [hzero] at hsub
      exact sub_eq_zero.mp hsub
  rw [hroots]
  exact traceFunction_rootSet_encard_le_two_global
    f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
    (tubePairDeltaD T U) hAB
    (by simpa [tubePairCoefficientDistance] using hcoefficient)
    hparameter hft hf1Lower hf1Upper hf2 hfDeriv hf1Deriv

#print axioms traceFunction_rootSet_encard_le_two_global
#print axioms tubeCinematicTrace_pair_rootSet_encard_le_two_global

end


end FamilyStickyCinematicL32GlobalTraceRootEncCardCleanV2
