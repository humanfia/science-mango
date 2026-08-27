import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55WideSourceFirstHitLabelWeightOwnerClusterCapV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteOccupiedCodeWideSourceFirstHitOwnerCapV1

open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma55FirstHitLabelWeightOwnerClusterCapV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
open FamilyStickyCinematicL32Lemma55WideSourceFirstHitLabelWeightOwnerClusterCapV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

universe u v w

/-!
# Wide first-hit cap for canonical occupied-code local outcomes

This is the package-free adapter from the honest wide-source geometry to the
finite-choice API used by the fixed-C third stage.  The code choice itself is
left untouched; the weight is fixed to the single global first-hit label
partition and therefore is not duplicated across codes.
-/

/-- Every canonical local selected pivot has the same explicit wide-source
owner-cluster cap. -/
theorem finiteOccupiedCodeLocalCompactClusterWeightAt_le_wideSourceFirstHitArea
    {code : Type u} {item : Type v} {label : Type w}
    [Fintype code] [DecidableEq code] [DecidableEq item] [DecidableEq label]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {localDelta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal)
    (source : Set (Real × Real)) (sourceLabels : Finset label)
    (sourceRectangle : label -> C2GraphRectangle)
    (labelAt : item -> label) (sourceDelta sourceScale : Real)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter localDelta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound)
    (hsource : MeasurableSet source)
    (hlabelMem : forall k, forall i, i ∈ rawAt k ->
      labelAt i ∈ sourceLabels)
    (hlabelInj : Function.Injective labelAt)
    (hsourceLength : forall k, forall i, i ∈ rawAt k ->
      (sourceRectangle (labelAt i)).rectangle.right -
          (sourceRectangle (labelAt i)).rectangle.left =
        Real.sqrt (sourceDelta / sourceScale))
    (hsourceBase : forall k, forall i, i ∈ rawAt k ->
      (sourceRectangle (labelAt i)).rectangle.base ⊆ domain)
    (hrectangle : forall k, forall i, i ∈ rawAt k ->
      rectangleAt i = exactLocalC2GraphRectangle
        (sourceRectangle (labelAt i)) localDelta localScale)
    (k : code) (pivot : item) :
    finiteOccupiedCodeLocalCompactClusterWeightAt rawAt rectangleAt domain
        localCenterAt globalCenter codeBound
        (fun _ i => firstHitLabelWeight source sourceLabels sourceRectangle
          sourceDelta labelAt i)
        G k pivot <=
      ENNReal.ofReal (2 * (sourceDelta + 6 * localScale)) *
        ENNReal.ofReal
          (Real.sqrt
              (pyzLemma312PackingLambda 100 * localDelta / localScale) +
            Real.sqrt (sourceDelta / sourceScale)) := by
  let weightAt : code -> item -> ENNReal := fun _ i =>
    firstHitLabelWeight source sourceLabels sourceRectangle sourceDelta
      labelAt i
  let C := finiteOccupiedCodeLocalCompactOutcome rawAt rectangleAt domain
    localCenterAt globalCenter codeBound weightAt G k
  have hcap :=
    wideSourceFirstHitLabelWeight_ownerClusterMass_le_explicitArea
      source sourceLabels sourceRectangle (rawAt k) labelAt rectangleAt
        domain (localCenterAt k) globalCenter localDelta localScale
          referenceScale comparisonLambda curvatureRatio centerGap sourceDelta
            sourceScale C hsource (hlabelMem k)
              (fun _i hi _j hj hij => hlabelInj hij) G.delta_pos.le
                (hsourceLength k) (hsourceBase k) (G.local_ball k)
                  (hrectangle k) pivot
  simpa only [finiteOccupiedCodeLocalCompactClusterWeightAt, weightAt, C]
    using hcap

#print axioms finiteOccupiedCodeLocalCompactClusterWeightAt_le_wideSourceFirstHitArea

end

end FamilyStickyCinematicL32FiniteOccupiedCodeWideSourceFirstHitOwnerCapV1
