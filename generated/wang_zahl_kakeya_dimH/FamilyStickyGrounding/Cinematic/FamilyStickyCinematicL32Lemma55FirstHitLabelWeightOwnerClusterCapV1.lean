import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapTwoCenterLocalCompactV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Lemma55FirstHitLabelWeightOwnerClusterCapV1

open FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterLocalCompactV1

noncomputable section

universe u v

/-!
# Package-free first-hit label weights in owner clusters

The global measurable partition is indexed once by source labels. Local
items merely pull those pieces back through an injective label map. This
prevents a local code refinement from duplicating first-hit mass while
remaining independent of any particular G-prime package.
-/

/-- Global first-hit label weight pulled back to a local item. -/
noncomputable def firstHitLabelWeight
    {label : Type u} [DecidableEq label]
    {item : Type v}
    (source : Set (Real × Real)) (sourceLabels : Finset label)
    (sourceRectangle : label -> C2GraphRectangle)
    (delta : Real) (labelAt : item -> label) (i : item) : ENNReal :=
  volume
    (firstHitFineRectangleY2 source sourceLabels sourceRectangle delta
      (labelAt i))

/-- First-hit pieces stay measurable after pullback along any item-label
map. -/
theorem measurableSet_firstHitLabelWeightPiece
    {label : Type u} [DecidableEq label]
    {item : Type v}
    (source : Set (Real × Real)) (sourceLabels : Finset label)
    (sourceRectangle : label -> C2GraphRectangle)
    (delta : Real) (labelAt : item -> label)
    (hsource : MeasurableSet source) (i : item) :
    MeasurableSet
      (firstHitFineRectangleY2 source sourceLabels sourceRectangle delta
        (labelAt i)) := by
  exact measurableSet_firstHitFineRectangleY2 source sourceLabels
    sourceRectangle delta hsource (labelAt i)

/-- Injectivity on the finite item carrier transfers global label
disjointness to the pulled-back item shadings. -/
theorem pairwiseDisjoint_firstHitLabelWeightPiece
    {label : Type u} [DecidableEq label]
    {item : Type v} [DecidableEq item]
    (source : Set (Real × Real)) (sourceLabels : Finset label)
    (sourceRectangle : label -> C2GraphRectangle)
    (delta : Real) (vertices : Finset item) (labelAt : item -> label)
    (hlabelMem : forall i, i ∈ vertices -> labelAt i ∈ sourceLabels)
    (hlabelInj : Set.InjOn labelAt (vertices : Set item)) :
    Set.PairwiseDisjoint (vertices : Set item)
      (fun i => firstHitFineRectangleY2 source sourceLabels sourceRectangle
        delta (labelAt i)) := by
  have hglobal :=
    firstHitFineRectangleY2_pairwiseDisjoint source sourceLabels
      sourceRectangle delta
  intro i hi j hj hij
  apply hglobal (hlabelMem i hi) (hlabelMem j hj)
  intro hlabels
  exact hij (hlabelInj hi hj hlabels)

/-- Package-free owner-cluster cap. The local rectangles need only agree
with the global source rectangle at each carried label. -/
theorem firstHitLabelWeight_ownerClusterMass_le_ownerDilation_twoCenterLocalCompact
    {label : Type u} [DecidableEq label]
    {item : Type v} [DecidableEq item]
    (source : Set (Real × Real)) (sourceLabels : Finset label)
    (sourceRectangle : label -> C2GraphRectangle)
    (vertices : Finset item) (labelAt : item -> label)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap : Real)
    (C : CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome vertices
      rectangleAt domain localCenter globalCenter delta localScale
        referenceScale comparisonLambda curvatureRatio centerGap
        (firstHitLabelWeight source sourceLabels sourceRectangle delta
          labelAt))
    (hsource : MeasurableSet source)
    (hlabelMem : forall i, i ∈ vertices -> labelAt i ∈ sourceLabels)
    (hlabelInj : Set.InjOn labelAt (vertices : Set item))
    (hrectangle : forall i, i ∈ vertices ->
      rectangleAt i = sourceRectangle (labelAt i))
    (pivot : item) :
    ownerClusterMass vertices C.owner
        (firstHitLabelWeight source sourceLabels sourceRectangle delta
          labelAt)
        pivot <=
      volume
        ((centeredC2GraphRectangleDilation (rectangleAt pivot) delta
          localScale (pyzLemma312PackingLambda 100)).carrier
            (pyzLemma312PackingLambda 100 * delta)) := by
  apply ownerClusterMass_measure_le_target volume vertices C.owner
    (fun i => firstHitFineRectangleY2 source sourceLabels sourceRectangle
      delta (labelAt i))
    pivot
    ((centeredC2GraphRectangleDilation (rectangleAt pivot) delta
      localScale (pyzLemma312PackingLambda 100)).carrier
        (pyzLemma312PackingLambda 100 * delta))
  · intro i _hi
    exact measurableSet_firstHitLabelWeightPiece source sourceLabels
      sourceRectangle delta labelAt hsource i
  · exact pairwiseDisjoint_firstHitLabelWeightPiece source sourceLabels
      sourceRectangle delta vertices labelAt hlabelMem hlabelInj
  · intro i hi howner
    have hfirst :
        firstHitFineRectangleY2 source sourceLabels sourceRectangle delta
            (labelAt i) ⊆
          (rectangleAt i).carrier delta := by
      rw [hrectangle i hi]
      exact firstHitFineRectangleY2_subset_carrier source sourceLabels
        sourceRectangle delta (labelAt i)
    exact hfirst.trans (by
      simpa only [howner] using C.cluster_carrier_subset i hi)

/-- Exact C2 carrier area gives the explicit dilation cap used by the
finite fixed-C mass outcome. -/
theorem firstHitLabelWeight_ownerClusterMass_le_explicitDilationArea_twoCenterLocalCompact
    {label : Type u} [DecidableEq label]
    {item : Type v} [DecidableEq item]
    (source : Set (Real × Real)) (sourceLabels : Finset label)
    (sourceRectangle : label -> C2GraphRectangle)
    (vertices : Finset item) (labelAt : item -> label)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap : Real)
    (C : CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome vertices
      rectangleAt domain localCenter globalCenter delta localScale
        referenceScale comparisonLambda curvatureRatio centerGap
        (firstHitLabelWeight source sourceLabels sourceRectangle delta
          labelAt))
    (hsource : MeasurableSet source)
    (hlabelMem : forall i, i ∈ vertices -> labelAt i ∈ sourceLabels)
    (hlabelInj : Set.InjOn labelAt (vertices : Set item))
    (hrectangle : forall i, i ∈ vertices ->
      rectangleAt i = sourceRectangle (labelAt i))
    (pivot : item) :
    ownerClusterMass vertices C.owner
        (firstHitLabelWeight source sourceLabels sourceRectangle delta
          labelAt)
        pivot <=
      ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
        ENNReal.ofReal
          (Real.sqrt
            (pyzLemma312PackingLambda 100 * delta / localScale)) := by
  calc
    ownerClusterMass vertices C.owner
        (firstHitLabelWeight source sourceLabels sourceRectangle delta
          labelAt)
        pivot <=
      volume
        ((centeredC2GraphRectangleDilation (rectangleAt pivot) delta
          localScale (pyzLemma312PackingLambda 100)).carrier
            (pyzLemma312PackingLambda 100 * delta)) :=
      firstHitLabelWeight_ownerClusterMass_le_ownerDilation_twoCenterLocalCompact
        source sourceLabels sourceRectangle vertices labelAt rectangleAt
          domain localCenter globalCenter delta localScale referenceScale
            comparisonLambda curvatureRatio centerGap C hsource hlabelMem
              hlabelInj hrectangle pivot
    _ = ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
        ENNReal.ofReal
          (Real.sqrt
            (pyzLemma312PackingLambda 100 * delta / localScale)) := by
      rw [volume_c2GraphRectangle_carrier,
        centeredC2GraphRectangleDilation_length]

#print axioms firstHitLabelWeight
#print axioms measurableSet_firstHitLabelWeightPiece
#print axioms pairwiseDisjoint_firstHitLabelWeightPiece
#print axioms firstHitLabelWeight_ownerClusterMass_le_ownerDilation_twoCenterLocalCompact
#print axioms firstHitLabelWeight_ownerClusterMass_le_explicitDilationArea_twoCenterLocalCompact

end

end FamilyStickyCinematicL32Lemma55FirstHitLabelWeightOwnerClusterCapV1
