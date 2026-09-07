import Family8Grounding.Family8Family7NativeHighActivePatternOccurrenceProducerV1
import Family8Grounding.Family8Family7NativeHighArbitraryWeightedProxySupportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighActivePatternScaleSplitV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7NativeHighActivePatternOccurrenceProducerV1
open Family8Family7NativeHighArbitraryWeightedCriticalScaleProxyV1
open Family8Family7NativeHighArbitraryWeightedProxySupportV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# Honest weighted-scale split for the native pattern occurrence

An arbitrary occurrence weight need not select a large critical scale.  The
literal alternative is retained: either its selected scale is below ten
times the native ball radius (the scale-restart branch), or the corresponding
affine proxy has radius at most one fifth and hence has unit-ball support.
-/

/-- The weighted norm datum selected by the native pattern-first mass. -/
noncomputable def nativeHighActivePatternWeightedNormData
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : WeightedCanonicalNormBallData iota :=
  nativeHighWeightedNormData D c
    (nativeHighActivePatternOccurrenceWeight D G c)

/-- On the complementary branch, the selected weighted scale is separated
from the physical tube radius by a factor of ten. -/
theorem ten_radius_le_nativeHighActivePatternCriticalScale_of_not_lt
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (hlarge : ¬(nativeHighActivePatternWeightedNormData D G c).criticalScale <
      10 * G.ballRadius c) :
    10 * (radius : Real) ≤
      (nativeHighActivePatternWeightedNormData D G c).criticalScale := by
  have hball : (radius : Real) ≤ G.ballRadius c := by
    simpa [positiveCenterHighPayloadGlobalNormData,
      actualGlobalNormIndexData] using G.hballRadiusLower c
  have htenBall : 10 * G.ballRadius c ≤
      (nativeHighActivePatternWeightedNormData D G c).criticalScale :=
    le_of_not_gt hlarge
  nlinarith

/-- The non-restart branch has the exact radius cap consumed by arbitrary
weighted proxy support and greedy admissibility. -/
theorem nativeHighActivePatternProxyRadius_le_one_fifth_of_not_lt
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (hlarge : ¬(nativeHighActivePatternWeightedNormData D G c).criticalScale <
      10 * G.ballRadius c) :
    let W := nativeHighActivePatternProxyInput D G c
    criticalScaleProxyRadius radius
        (nativeHighWeightedNormData D W.center W.weight).criticalScale
        (nativeHighArbitraryWeightedCriticalScale_pos D W) ≤
      (1 / 5 : NNReal) := by
  dsimp only [nativeHighActivePatternProxyInput,
    nativeHighActivePatternWeightedNormData]
  apply criticalScaleProxyRadius_le_one_fifth
  exact ten_radius_le_nativeHighActivePatternCriticalScale_of_not_lt
    D G c hlarge

/-- No false uniform cap is asserted: every native pattern-weighted choice
lands in exactly one of the honest restart or supported-proxy branches. -/
theorem nativeHighActivePattern_scaleRestart_or_proxyRadius_le_one_fifth
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    (nativeHighActivePatternWeightedNormData D G c).criticalScale <
        10 * G.ballRadius c ∨
      let W := nativeHighActivePatternProxyInput D G c
      criticalScaleProxyRadius radius
          (nativeHighWeightedNormData D W.center W.weight).criticalScale
          (nativeHighArbitraryWeightedCriticalScale_pos D W) ≤
        (1 / 5 : NNReal) := by
  by_cases hscale :
      (nativeHighActivePatternWeightedNormData D G c).criticalScale <
        10 * G.ballRadius c
  · exact Or.inl hscale
  · exact Or.inr
      (nativeHighActivePatternProxyRadius_le_one_fifth_of_not_lt
        D G c hscale)

/-- Upstream unit-ball support for the original ambient family transfers
automatically on the non-restart branch. -/
theorem nativeHighActivePatternProxyFamily_contained_in_unit_ball_of_not_lt
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (hambientSource : D.ambient ⊆ D.S.source)
    (hcontained : ∀ i, i ∈ D.ambient →
      (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hlarge : ¬(nativeHighActivePatternWeightedNormData D G c).criticalScale <
      10 * G.ballRadius c) :
    let W := nativeHighActivePatternProxyInput D G c
    ∀ i : NativeHighArbitraryWeightedCriticalBallIndex D W,
      ((nativeHighArbitraryWeightedCriticalScaleProxyFamily
        D W).tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
  dsimp only
  apply nativeHighArbitraryWeightedProxyFamily_contained_in_unit_ball
    D (nativeHighActivePatternProxyInput D G c) hambientSource hcontained
  exact nativeHighActivePatternProxyRadius_le_one_fifth_of_not_lt
    D G c hlarge

#print axioms nativeHighActivePatternWeightedNormData
#print axioms
  ten_radius_le_nativeHighActivePatternCriticalScale_of_not_lt
#print axioms
  nativeHighActivePatternProxyRadius_le_one_fifth_of_not_lt
#print axioms
  nativeHighActivePattern_scaleRestart_or_proxyRadius_le_one_fifth
#print axioms
  nativeHighActivePatternProxyFamily_contained_in_unit_ball_of_not_lt

end

end Family8Family7NativeHighActivePatternScaleSplitV1
