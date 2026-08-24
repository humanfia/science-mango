import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32OscillationProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualOppositeEndpointRootEncCardV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualRootEncCardV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtPairEncCardV1
import Submission.Kakeya.ConvexGeometry.Tube

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32Prop41ActualRootEncCardV1
open FamilyStickyCinematicL32Prop41ActualOppositeEndpointRootEncCardV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41RectangularSkirtPairEncCardV1

noncomputable section

/-!
# Actual tube-pair cardinality for rectangular skirts

This module identifies graph equality with the literal Wang--Zahl trace root
set.  The same-endpoint-order branch gets `encard <= 2` from the actual
twice-Rolle theorem and its short-interval oscillation producer.  In the
endpoint-reversal branch the global jet trichotomy gives `encard <= 1`, which
is then combined with the unique exterior crossing.
-/

def skirtTubeGraphC {radius : NNReal} (T : Tube radius) : Real :=
  T.axis.direction 0 / T.axis.direction 2

def skirtTubeGraphD {radius : NNReal} (T : Tube radius) : Real :=
  T.axis.direction 1 / T.axis.direction 2

def skirtTubeGraphA {radius : NNReal} (T : Tube radius) : Real :=
  T.axis.base 0 - skirtTubeGraphC T * T.axis.base 2

def skirtTubeGraphB {radius : NNReal} (T : Tube radius) : Real :=
  T.axis.base 1 - skirtTubeGraphD T * T.axis.base 2

def skirtTubePairDeltaA {radius : NNReal} (T U : Tube radius) : Real :=
  skirtTubeGraphA T - skirtTubeGraphA U

def skirtTubePairDeltaB {radius : NNReal} (T U : Tube radius) : Real :=
  skirtTubeGraphB T - skirtTubeGraphB U

def skirtTubePairDeltaD {radius : NNReal} (T U : Tube radius) : Real :=
  skirtTubeGraphD T - skirtTubeGraphD U

def skirtTubePairCoefficientDistance {radius : NNReal}
    (T U : Tube radius) : Real :=
  coefficientDistance (skirtTubePairDeltaA T U)
    (skirtTubePairDeltaB T U) (skirtTubePairDeltaD T U)

def actualTubeGraph {radius : NNReal} (T : Tube radius)
    (f : Real -> Real) : Real -> Real :=
  fun theta => skirtTubeGraphA T + skirtTubeGraphC T * theta +
    f theta * (skirtTubeGraphB T + skirtTubeGraphD T * theta)

theorem actualTubeGraph_sub_eq_traceFunction
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (hcommonC : skirtTubeGraphC T = skirtTubeGraphC U) (theta : Real) :
    actualTubeGraph T f theta - actualTubeGraph U f theta =
      traceFunction f (skirtTubePairDeltaA T U) (skirtTubePairDeltaB T U)
        (skirtTubePairDeltaD T U) theta := by
  simp only [actualTubeGraph, traceFunction,
    FamilyStickyCinematicL32JetSeparationV1.traceJet0,
    skirtTubePairDeltaA, skirtTubePairDeltaB, skirtTubePairDeltaD]
  rw [hcommonC]
  ring

theorem actualTubeGraph_rootSet_eq_traceFunction_rootSet
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (hcommonC : skirtTubeGraphC T = skirtTubeGraphC U) (A B : Real) :
    {theta | theta ∈ Icc A B ∧ actualTubeGraph T f theta =
      actualTubeGraph U f theta} =
    {theta | theta ∈ Icc A B ∧
      traceFunction f (skirtTubePairDeltaA T U) (skirtTubePairDeltaB T U)
        (skirtTubePairDeltaD T U) theta = 0} := by
  ext theta
  constructor
  · rintro ⟨htheta, heq⟩
    refine ⟨htheta, ?_⟩
    rw [← actualTubeGraph_sub_eq_traceFunction T U f hcommonC, heq, sub_self]
  · rintro ⟨htheta, hzero⟩
    refine ⟨htheta, ?_⟩
    have hsub := actualTubeGraph_sub_eq_traceFunction T U f hcommonC theta
    rw [hzero] at hsub
    linarith

theorem actual_rectangularSkirtCurve_inter_encard_le_two_of_same_endpoint_order
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) (A B M d e : Real)
    (hAB : A < B) (hd : 0 < d) (he : 0 < e) (hde : d < e)
    (hcommonC : skirtTubeGraphC T = skirtTubeGraphC U)
    (hcoefficient : 0 < skirtTubePairCoefficientDistance T U)
    (hshort : B - A < 1 / 6000)
    (hleft : actualTubeGraph T f A < actualTubeGraph U f A)
    (hright : actualTubeGraph T f B < actualTubeGraph U f B)
    (hTLower : forall theta, theta ∈ Icc A B ->
      -M <= actualTubeGraph T f theta)
    (hULower : forall theta, theta ∈ Icc A B ->
      -M <= actualTubeGraph U f theta)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f1 (f2 theta) theta) :
    (rectangularSkirtCurve (actualTubeGraph T f) A B M d ∩
      rectangularSkirtCurve (actualTubeGraph U f) A B M e).encard <= 2 := by
  obtain ⟨hosc0, hosc1⟩ := traceFunction_oscillations_on_short_Icc
    f f1 f2 (skirtTubePairDeltaA T U) (skirtTubePairDeltaB T U)
      (skirtTubePairDeltaD T U)
      (by simpa [skirtTubePairCoefficientDistance] using hcoefficient)
      hshort hparameter hft hf1Upper hf2 hfDeriv hf1Deriv
  have htraceRoots := traceFunction_rootSet_encard_le_two
    f f1 f2 (skirtTubePairDeltaA T U) (skirtTubePairDeltaB T U)
      (skirtTubePairDeltaD T U)
      (by simpa [skirtTubePairCoefficientDistance] using hcoefficient)
      hparameter hft hf1Lower hf1Upper hf2 hfDeriv hf1Deriv hosc0 hosc1
  apply rectangularSkirtCurve_inter_encard_le_two_of_same_endpoint_order
    (actualTubeGraph T f) (actualTubeGraph U f) A B M d e
    hAB hd he hde hleft hright hTLower hULower
  rw [actualTubeGraph_rootSet_eq_traceFunction_rootSet T U f hcommonC A B]
  exact htraceRoots

theorem actual_rectangularSkirtCurve_inter_encard_le_two_of_reversed_endpoint_order
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) (A B M d e : Real)
    (hAB : A < B) (hd : 0 < d) (he : 0 < e) (hde : d < e)
    (hcommonC : skirtTubeGraphC T = skirtTubeGraphC U)
    (hcoefficient : 0 < skirtTubePairCoefficientDistance T U)
    (hleft : actualTubeGraph T f A < actualTubeGraph U f A)
    (hright : actualTubeGraph U f B < actualTubeGraph T f B)
    (hTLower : forall theta, theta ∈ Icc A B ->
      -M <= actualTubeGraph T f theta)
    (hULower : forall theta, theta ∈ Icc A B ->
      -M <= actualTubeGraph U f theta)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f1 (f2 theta) theta)
    (hf2Continuous : ContinuousOn f2 (Icc A B)) :
    (rectangularSkirtCurve (actualTubeGraph T f) A B M d ∩
      rectangularSkirtCurve (actualTubeGraph U f) A B M e).encard <= 2 := by
  have htraceLeft : traceFunction f
      (skirtTubePairDeltaA T U) (skirtTubePairDeltaB T U)
      (skirtTubePairDeltaD T U) A < 0 := by
    rw [← actualTubeGraph_sub_eq_traceFunction T U f hcommonC]
    linarith
  have htraceRight : 0 < traceFunction f
      (skirtTubePairDeltaA T U) (skirtTubePairDeltaB T U)
      (skirtTubePairDeltaD T U) B := by
    rw [← actualTubeGraph_sub_eq_traceFunction T U f hcommonC]
    linarith
  have htraceRoots := traceFunction_oppositeEndpoint_rootSet_encard_le_one
    f f1 f2 (skirtTubePairDeltaA T U) (skirtTubePairDeltaB T U)
      (skirtTubePairDeltaD T U) hAB
      (by simpa [skirtTubePairCoefficientDistance] using hcoefficient)
      htraceLeft htraceRight hparameter hft hf1Lower hf1Upper hf2
      hfDeriv hf1Deriv hf2Continuous
  apply rectangularSkirtCurve_inter_encard_le_two_of_reversed_endpoint_order
    (actualTubeGraph T f) (actualTubeGraph U f) A B M d e
    hAB hd he hde hleft hright hTLower hULower
  rw [actualTubeGraph_rootSet_eq_traceFunction_rootSet T U f hcommonC A B]
  exact htraceRoots

#print axioms actualTubeGraph_sub_eq_traceFunction
#print axioms actualTubeGraph_rootSet_eq_traceFunction_rootSet
#print axioms actual_rectangularSkirtCurve_inter_encard_le_two_of_same_endpoint_order
#print axioms actual_rectangularSkirtCurve_inter_encard_le_two_of_reversed_endpoint_order

end

end FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
