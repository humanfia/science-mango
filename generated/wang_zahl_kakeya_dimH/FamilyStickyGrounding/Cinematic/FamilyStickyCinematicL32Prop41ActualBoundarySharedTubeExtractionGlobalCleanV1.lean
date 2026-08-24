import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32GlobalTraceRootEncCardCleanV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GraphLensBoundarySharedSideExtractionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairTraceV1
import Submission.Kakeya.ConvexGeometry.Tube

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ActualBoundarySharedTubeExtractionGlobalCleanV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32GlobalTraceRootEncCardCleanV2
open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1
open FamilyStickyCinematicL32Prop41GraphLensBoundarySharedSideExtractionV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Long-interval actual boundary shared-side extraction

This is the non-vacuous replacement for the old short-interval extraction.
It uses the global coefficient-jet root bound, so the same ambient interval
may simultaneously satisfy the width hypothesis needed by lens localization.
-/

def actualPairGraphBoundary {radius : NNReal}
    (T U : Tube radius) (f : Real -> Real)
    (left right : Real) : Set (Real × Real) :=
  graphLensBoundaryArcs
    (cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
      (tubeGraphC T) (tubeGraphD T))
    (cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
      (tubeGraphC U) (tubeGraphD U))
    left right

private theorem actualTubePair_rootSet_finite_global
    {radius : NNReal} (curves : Finset (Tube radius))
    (f f1 f2 : Real -> Real) {A B : Real}
    (hAB : A <= B)
    (hcommonC : forall T, T ∈ curves -> forall U, U ∈ curves ->
      tubeGraphC T = tubeGraphC U)
    (hcoefficient : forall T, T ∈ curves -> forall U, U ∈ curves ->
      T ≠ U -> 0 < tubePairCoefficientDistance T U)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f1 (f2 theta) theta)
    (T : Tube radius) (hT : T ∈ curves)
    (U : Tube radius) (hU : U ∈ curves) (hTU : T ≠ U) :
    {theta | theta ∈ Icc A B ∧
      cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T) theta =
        cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U) theta}.Finite := by
  exact Set.finite_of_encard_le_coe
    (tubeCinematicTrace_pair_rootSet_encard_le_two_global T U f f1 f2
      hAB (hcommonC T hT U hU) (hcoefficient T hT U hU hTU)
      hparameter hft hf1Lower hf1Upper hf2 hfDeriv hf1Deriv)

private theorem actualTubePair_supportedGraphArcs_inter_finite_global
    {radius : NNReal} (curves : Finset (Tube radius))
    (f f1 f2 : Real -> Real) {A B : Real}
    (hAB : A <= B)
    (hcommonC : forall T, T ∈ curves -> forall U, U ∈ curves ->
      tubeGraphC T = tubeGraphC U)
    (hcoefficient : forall T, T ∈ curves -> forall U, U ∈ curves ->
      T ≠ U -> 0 < tubePairCoefficientDistance T U)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f1 (f2 theta) theta)
    (V : Tube radius) (hV : V ∈ curves)
    (W : Tube radius) (hW : W ∈ curves) (hVW : V ≠ W)
    {leftV rightV leftW rightW : Real}
    (hleftV : leftV ∈ Icc A B) (hrightV : rightV ∈ Icc A B)
    (hleftW : leftW ∈ Icc A B) (hrightW : rightW ∈ Icc A B) :
    (graphArc
        (cinematicTraceValue f (tubeGraphA V) (tubeGraphB V)
          (tubeGraphC V) (tubeGraphD V)) (Icc leftV rightV) ∩
      graphArc
        (cinematicTraceValue f (tubeGraphA W) (tubeGraphB W)
          (tubeGraphC W) (tubeGraphD W)) (Icc leftW rightW)).Finite := by
  let gV := cinematicTraceValue f (tubeGraphA V) (tubeGraphB V)
    (tubeGraphC V) (tubeGraphD V)
  let gW := cinematicTraceValue f (tubeGraphA W) (tubeGraphB W)
    (tubeGraphC W) (tubeGraphD W)
  have hroots : {theta | theta ∈ Icc A B ∧ gV theta = gW theta}.Finite := by
    simpa [gV, gW] using actualTubePair_rootSet_finite_global curves
      f f1 f2 hAB hcommonC hcoefficient hparameter hft hf1Lower
      hf1Upper hf2 hfDeriv hf1Deriv V hV W hW hVW
  apply (hroots.image (fun theta : Real => (gV theta, theta))).subset
  intro q hq
  rcases hq with ⟨hqV, hqW⟩
  have hqABV : q.2 ∈ Icc A B :=
    ⟨hleftV.1.trans hqV.1.1, hqV.1.2.trans hrightV.2⟩
  have hqABW : q.2 ∈ Icc A B :=
    ⟨hleftW.1.trans hqW.1.1, hqW.1.2.trans hrightW.2⟩
  have hqAB : q.2 ∈ Icc A B := ⟨hqABV.1, hqABW.2⟩
  refine ⟨q.2, ⟨hqAB, hqV.2.symm.trans hqW.2⟩, ?_⟩
  exact Prod.ext hqV.2.symm rfl

/-- A positive shared boundary segment exposes a literal shared side tube.
No shortness hypothesis is present. -/
theorem exists_equal_cross_side_tubes_of_actualPairBoundaries_sharePositiveSegment_global
    {radius : NNReal} (curves : Finset (Tube radius))
    (f f1 f2 : Real -> Real) {A B : Real}
    (hAB : A <= B)
    (hcommonC : forall T, T ∈ curves -> forall U, U ∈ curves ->
      tubeGraphC T = tubeGraphC U)
    (hcoefficient : forall T, T ∈ curves -> forall U, U ∈ curves ->
      T ≠ U -> 0 < tubePairCoefficientDistance T U)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f1 (f2 theta) theta)
    (T1 : Tube radius) (hT1 : T1 ∈ curves)
    (U1 : Tube radius) (hU1 : U1 ∈ curves)
    (T2 : Tube radius) (hT2 : T2 ∈ curves)
    (U2 : Tube radius) (hU2 : U2 ∈ curves)
    {left1 right1 left2 right2 : Real}
    (hleft1 : left1 ∈ Icc A B) (hright1 : right1 ∈ Icc A B)
    (hleft2 : left2 ∈ Icc A B) (hright2 : right2 ∈ Icc A B)
    (hoverlap : sharePositiveGraphSegment
      (actualPairGraphBoundary T1 U1 f left1 right1)
      (actualPairGraphBoundary T2 U2 f left2 right2)) :
    T1 = T2 ∨ T1 = U2 ∨ U1 = T2 ∨ U1 = U2 := by
  have hinfinite :=
    exists_nonfinite_cross_side_intersection_of_sharePositiveGraphSegment
      (cinematicTraceValue f (tubeGraphA T1) (tubeGraphB T1)
        (tubeGraphC T1) (tubeGraphD T1))
      (cinematicTraceValue f (tubeGraphA U1) (tubeGraphB U1)
        (tubeGraphC U1) (tubeGraphD U1))
      (cinematicTraceValue f (tubeGraphA T2) (tubeGraphB T2)
        (tubeGraphC T2) (tubeGraphD T2))
      (cinematicTraceValue f (tubeGraphA U2) (tubeGraphB U2)
        (tubeGraphC U2) (tubeGraphD U2))
      (Icc left1 right1) (Icc left2 right2)
      (by simpa [actualPairGraphBoundary, graphLensBoundaryArcs] using hoverlap)
  by_contra hnone
  simp only [not_or] at hnone
  rcases hnone with ⟨hT1T2, hT1U2, hU1T2, hU1U2⟩
  rcases hinfinite with hinfinite | hinfinite | hinfinite | hinfinite
  · exact hinfinite (actualTubePair_supportedGraphArcs_inter_finite_global
      curves f f1 f2 hAB hcommonC hcoefficient hparameter hft hf1Lower
      hf1Upper hf2 hfDeriv hf1Deriv T1 hT1 T2 hT2 hT1T2
      hleft1 hright1 hleft2 hright2)
  · exact hinfinite (actualTubePair_supportedGraphArcs_inter_finite_global
      curves f f1 f2 hAB hcommonC hcoefficient hparameter hft hf1Lower
      hf1Upper hf2 hfDeriv hf1Deriv T1 hT1 U2 hU2 hT1U2
      hleft1 hright1 hleft2 hright2)
  · exact hinfinite (actualTubePair_supportedGraphArcs_inter_finite_global
      curves f f1 f2 hAB hcommonC hcoefficient hparameter hft hf1Lower
      hf1Upper hf2 hfDeriv hf1Deriv U1 hU1 T2 hT2 hU1T2
      hleft1 hright1 hleft2 hright2)
  · exact hinfinite (actualTubePair_supportedGraphArcs_inter_finite_global
      curves f f1 f2 hAB hcommonC hcoefficient hparameter hft hf1Lower
      hf1Upper hf2 hfDeriv hf1Deriv U1 hU1 U2 hU2 hU1U2
      hleft1 hright1 hleft2 hright2)

#print axioms actualPairGraphBoundary
#print axioms exists_equal_cross_side_tubes_of_actualPairBoundaries_sharePositiveSegment_global

end

end FamilyStickyCinematicL32Prop41ActualBoundarySharedTubeExtractionGlobalCleanV1
