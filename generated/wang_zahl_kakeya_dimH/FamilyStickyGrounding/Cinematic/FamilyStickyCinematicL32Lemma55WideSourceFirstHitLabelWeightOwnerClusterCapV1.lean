import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FirstHitLabelWeightOwnerClusterCapV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Lemma55WideSourceFirstHitLabelWeightOwnerClusterCapV1

open FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Lemma55FirstHitLabelWeightOwnerClusterCapV1
open FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterLocalCompactV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

universe u v

/-!
# First-hit owner cap for a source rectangle wider than the local rectangle

The global first-hit partition is cut out using the paper fine rectangle at
`sourceDelta`.  The local greedy clustering instead uses
`exactLocalC2GraphRectangle` at `localDelta`.  These rectangles have the
same graph, jets, and centre, but they are not equal and their carriers must
not be identified.

This module gives the honest bridge.  The local cluster containment controls
the distance between the item and owner centres.  The additional source
half-width is then added literally.  On the wider source base, membership in
one local pointwise C2 ball bounds the two graph values by
`6 * localScale`, so the vertical radius is enlarged to
`sourceDelta + 6 * localScale`.
-/

/-- A literal pivot-centred container wide enough for a global source
rectangle whose exact-local restriction belongs to one owner cluster. -/
def wideSourceFirstHitOwnerContainer
    (R : C2GraphRectangle)
    (localDelta localScale sourceDelta sourceScale : Real) :
    C2GraphRectangle where
  rectangle :=
    { graph := R.rectangle.graph
      left := graphRectangleCenter R.rectangle -
        (Real.sqrt
            (pyzLemma312PackingLambda 100 * localDelta / localScale) +
          Real.sqrt (sourceDelta / sourceScale)) / 2
      right := graphRectangleCenter R.rectangle +
        (Real.sqrt
            (pyzLemma312PackingLambda 100 * localDelta / localScale) +
          Real.sqrt (sourceDelta / sourceScale)) / 2
      left_le_right := by
        nlinarith [Real.sqrt_nonneg
          (pyzLemma312PackingLambda 100 * localDelta / localScale),
          Real.sqrt_nonneg (sourceDelta / sourceScale)] }
  first := R.first
  second := R.second
  graph_hasDeriv := R.graph_hasDeriv
  first_hasDeriv := R.first_hasDeriv

@[simp]
theorem wideSourceFirstHitOwnerContainer_length
    (R : C2GraphRectangle)
    (localDelta localScale sourceDelta sourceScale : Real) :
    (wideSourceFirstHitOwnerContainer R localDelta localScale sourceDelta
        sourceScale).rectangle.right -
      (wideSourceFirstHitOwnerContainer R localDelta localScale sourceDelta
        sourceScale).rectangle.left =
      Real.sqrt
          (pyzLemma312PackingLambda 100 * localDelta / localScale) +
        Real.sqrt (sourceDelta / sourceScale) := by
  simp [wideSourceFirstHitOwnerContainer]

/-- A wide source carrier lies in the explicit wide container of its local
owner.  The only relation between the two rectangle families is the honest
exact-local identity; equality of the wide and local rectangles is not
assumed. -/
theorem sourceRectangle_carrier_subset_wideSourceFirstHitOwnerContainer
    {label : Type u} [DecidableEq label]
    {item : Type v} [DecidableEq item]
    {weight : item -> ENNReal}
    (sourceRectangle : label -> C2GraphRectangle)
    (vertices : Finset item) (labelAt : item -> label)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    (localDelta localScale referenceScale comparisonLambda curvatureRatio
      centerGap sourceDelta sourceScale : Real)
    (C : CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome vertices
      rectangleAt domain localCenter globalCenter localDelta localScale
        referenceScale comparisonLambda curvatureRatio centerGap weight)
    (hlocalDelta : 0 <= localDelta)
    (hsourceLength : forall i, i ∈ vertices ->
      (sourceRectangle (labelAt i)).rectangle.right -
          (sourceRectangle (labelAt i)).rectangle.left =
        Real.sqrt (sourceDelta / sourceScale))
    (hsourceBase : forall i, i ∈ vertices ->
      (sourceRectangle (labelAt i)).rectangle.base ⊆ domain)
    (hballLocal : forall i, i ∈ vertices ->
      InPointwiseC2BallOn domain localCenter
        (rectangleAt i) (3 * localScale))
    (hrectangle : forall i, i ∈ vertices ->
      rectangleAt i = exactLocalC2GraphRectangle
        (sourceRectangle (labelAt i)) localDelta localScale)
    (i : item) (hi : i ∈ vertices) :
    (sourceRectangle (labelAt i)).carrier sourceDelta ⊆
      (wideSourceFirstHitOwnerContainer (rectangleAt (C.owner i))
        localDelta localScale sourceDelta sourceScale).carrier
          (sourceDelta + 6 * localScale) := by
  intro q hq
  let itemCenter := graphRectangleCenter (rectangleAt i).rectangle
  let ownerCenter := graphRectangleCenter
    (rectangleAt (C.owner i)).rectangle
  have hownerVertex : C.owner i ∈ vertices :=
    C.pivots_subset (C.owner_mem i hi)
  have hitemCenterBase :
      itemCenter ∈ (rectangleAt i).rectangle.base := by
    dsimp only [itemCenter, graphRectangleCenter,
      FamilyStickyCinematicL32CurvilinearRectangleCarrierV1.GraphRectangle.base]
    constructor <;>
      linarith [(rectangleAt i).rectangle.left_le_right]
  have hitemCenterCarrier :
      ((rectangleAt i).rectangle.graph itemCenter, itemCenter) ∈
        (rectangleAt i).carrier localDelta := by
    refine ⟨hitemCenterBase, ?_⟩
    simpa using hlocalDelta
  have hitemCenterInOwnerLocal :=
    C.cluster_carrier_subset i hi hitemCenterCarrier |>.1
  have hitemCenterLocalBounds : itemCenter ∈ Icc
      (ownerCenter -
        Real.sqrt
          (pyzLemma312PackingLambda 100 * localDelta / localScale) / 2)
      (ownerCenter +
        Real.sqrt
          (pyzLemma312PackingLambda 100 * localDelta / localScale) / 2) := by
    simpa only [ownerCenter, centeredC2GraphRectangleDilation,
      FamilyStickyCinematicL32CurvilinearRectangleCarrierV1.GraphRectangle.base]
      using hitemCenterInOwnerLocal
  have hcenterEq : itemCenter =
      graphRectangleCenter (sourceRectangle (labelAt i)).rectangle := by
    dsimp only [itemCenter]
    rw [hrectangle i hi]
    dsimp only [exactLocalC2GraphRectangle,
      centeredC2GraphRectangleDilation, graphRectangleCenter]
    ring
  have hqSourceBounds := hq.1
  have hqItemBounds : q.2 ∈ Icc
      (itemCenter - Real.sqrt (sourceDelta / sourceScale) / 2)
      (itemCenter + Real.sqrt (sourceDelta / sourceScale) / 2) := by
    rw [hcenterEq]
    dsimp only [graphRectangleCenter,
      FamilyStickyCinematicL32CurvilinearRectangleCarrierV1.GraphRectangle.base]
      at hqSourceBounds ⊢
    have hlength := hsourceLength i hi
    constructor <;>
      linarith [hqSourceBounds.1, hqSourceBounds.2, hlength]
  have htargetBase : q.2 ∈
      (wideSourceFirstHitOwnerContainer (rectangleAt (C.owner i))
        localDelta localScale sourceDelta sourceScale).rectangle.base := by
    change q.2 ∈ Icc
      (ownerCenter -
        (Real.sqrt
            (pyzLemma312PackingLambda 100 * localDelta / localScale) +
          Real.sqrt (sourceDelta / sourceScale)) / 2)
      (ownerCenter +
        (Real.sqrt
            (pyzLemma312PackingLambda 100 * localDelta / localScale) +
          Real.sqrt (sourceDelta / sourceScale)) / 2)
    constructor <;>
      linarith [hitemCenterLocalBounds.1, hitemCenterLocalBounds.2,
        hqItemBounds.1, hqItemBounds.2]
  have hqDomain : q.2 ∈ domain := hsourceBase i hi hq.1
  have hiGraph := (hballLocal i hi q.2 hqDomain).1
  have hownerGraph :=
    (hballLocal (C.owner i) hownerVertex q.2 hqDomain).1
  have hsourceGraph :
      (sourceRectangle (labelAt i)).rectangle.graph =
        (rectangleAt i).rectangle.graph := by
    rw [hrectangle i hi]
    rfl
  have hgraphDifference :
      |(sourceRectangle (labelAt i)).rectangle.graph q.2 -
          (rectangleAt (C.owner i)).rectangle.graph q.2| <=
        6 * localScale := by
    rw [hsourceGraph]
    calc
      |(rectangleAt i).rectangle.graph q.2 -
          (rectangleAt (C.owner i)).rectangle.graph q.2| =
        |((rectangleAt i).rectangle.graph q.2 -
            localCenter.rectangle.graph q.2) +
          (localCenter.rectangle.graph q.2 -
            (rectangleAt (C.owner i)).rectangle.graph q.2)| := by
              congr 1
              ring
      _ <= |(rectangleAt i).rectangle.graph q.2 -
            localCenter.rectangle.graph q.2| +
          |localCenter.rectangle.graph q.2 -
            (rectangleAt (C.owner i)).rectangle.graph q.2| :=
        abs_add_le _ _
      _ = |(rectangleAt i).rectangle.graph q.2 -
            localCenter.rectangle.graph q.2| +
          |(rectangleAt (C.owner i)).rectangle.graph q.2 -
            localCenter.rectangle.graph q.2| := by
        rw [abs_sub_comm (localCenter.rectangle.graph q.2)]
      _ <= 3 * localScale + 3 * localScale :=
        add_le_add hiGraph hownerGraph
      _ = 6 * localScale := by ring
  have htargetVertical :
      |q.1 - (rectangleAt (C.owner i)).rectangle.graph q.2| <=
        sourceDelta + 6 * localScale := by
    calc
      |q.1 - (rectangleAt (C.owner i)).rectangle.graph q.2| =
        |(q.1 - (sourceRectangle (labelAt i)).rectangle.graph q.2) +
          ((sourceRectangle (labelAt i)).rectangle.graph q.2 -
            (rectangleAt (C.owner i)).rectangle.graph q.2)| := by
              congr 1
              ring
      _ <= |q.1 - (sourceRectangle (labelAt i)).rectangle.graph q.2| +
          |(sourceRectangle (labelAt i)).rectangle.graph q.2 -
            (rectangleAt (C.owner i)).rectangle.graph q.2| :=
        abs_add_le _ _
      _ <= sourceDelta + 6 * localScale :=
        add_le_add hq.2 hgraphDifference
  exact ⟨htargetBase, by
    simpa only [wideSourceFirstHitOwnerContainer] using htargetVertical⟩

/-- First-hit owner mass for global wide source rectangles is bounded by
the volume of the honest wide owner container. -/
theorem wideSourceFirstHitLabelWeight_ownerClusterMass_le_ownerContainer
    {label : Type u} [DecidableEq label]
    {item : Type v} [DecidableEq item]
    (source : Set (Real × Real)) (sourceLabels : Finset label)
    (sourceRectangle : label -> C2GraphRectangle)
    (vertices : Finset item) (labelAt : item -> label)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    (localDelta localScale referenceScale comparisonLambda curvatureRatio
      centerGap sourceDelta sourceScale : Real)
    (C : CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome vertices
      rectangleAt domain localCenter globalCenter localDelta localScale
        referenceScale comparisonLambda curvatureRatio centerGap
        (firstHitLabelWeight source sourceLabels sourceRectangle sourceDelta
          labelAt))
    (hsource : MeasurableSet source)
    (hlabelMem : forall i, i ∈ vertices -> labelAt i ∈ sourceLabels)
    (hlabelInj : Set.InjOn labelAt (vertices : Set item))
    (hlocalDelta : 0 <= localDelta)
    (hsourceLength : forall i, i ∈ vertices ->
      (sourceRectangle (labelAt i)).rectangle.right -
          (sourceRectangle (labelAt i)).rectangle.left =
        Real.sqrt (sourceDelta / sourceScale))
    (hsourceBase : forall i, i ∈ vertices ->
      (sourceRectangle (labelAt i)).rectangle.base ⊆ domain)
    (hballLocal : forall i, i ∈ vertices ->
      InPointwiseC2BallOn domain localCenter
        (rectangleAt i) (3 * localScale))
    (hrectangle : forall i, i ∈ vertices ->
      rectangleAt i = exactLocalC2GraphRectangle
        (sourceRectangle (labelAt i)) localDelta localScale)
    (pivot : item) :
    ownerClusterMass vertices C.owner
        (firstHitLabelWeight source sourceLabels sourceRectangle sourceDelta
          labelAt)
        pivot <=
      volume
        ((wideSourceFirstHitOwnerContainer (rectangleAt pivot)
          localDelta localScale sourceDelta sourceScale).carrier
            (sourceDelta + 6 * localScale)) := by
  apply ownerClusterMass_measure_le_target volume vertices C.owner
    (fun i => firstHitFineRectangleY2 source sourceLabels sourceRectangle
      sourceDelta (labelAt i))
    pivot
    ((wideSourceFirstHitOwnerContainer (rectangleAt pivot)
      localDelta localScale sourceDelta sourceScale).carrier
        (sourceDelta + 6 * localScale))
  · intro i _hi
    exact measurableSet_firstHitLabelWeightPiece source sourceLabels
      sourceRectangle sourceDelta labelAt hsource i
  · exact pairwiseDisjoint_firstHitLabelWeightPiece source sourceLabels
      sourceRectangle sourceDelta vertices labelAt hlabelMem hlabelInj
  · intro i hi howner
    apply (firstHitFineRectangleY2_subset_carrier source sourceLabels
      sourceRectangle sourceDelta (labelAt i)).trans
    have hwide :=
      sourceRectangle_carrier_subset_wideSourceFirstHitOwnerContainer
        sourceRectangle vertices labelAt rectangleAt domain localCenter
          globalCenter localDelta localScale referenceScale comparisonLambda
            curvatureRatio centerGap sourceDelta sourceScale C hlocalDelta
              hsourceLength hsourceBase hballLocal hrectangle i hi
    simpa only [howner] using hwide

/-- Exact carrier area of the wide owner container. -/
theorem wideSourceFirstHitLabelWeight_ownerClusterMass_le_explicitArea
    {label : Type u} [DecidableEq label]
    {item : Type v} [DecidableEq item]
    (source : Set (Real × Real)) (sourceLabels : Finset label)
    (sourceRectangle : label -> C2GraphRectangle)
    (vertices : Finset item) (labelAt : item -> label)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    (localDelta localScale referenceScale comparisonLambda curvatureRatio
      centerGap sourceDelta sourceScale : Real)
    (C : CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome vertices
      rectangleAt domain localCenter globalCenter localDelta localScale
        referenceScale comparisonLambda curvatureRatio centerGap
        (firstHitLabelWeight source sourceLabels sourceRectangle sourceDelta
          labelAt))
    (hsource : MeasurableSet source)
    (hlabelMem : forall i, i ∈ vertices -> labelAt i ∈ sourceLabels)
    (hlabelInj : Set.InjOn labelAt (vertices : Set item))
    (hlocalDelta : 0 <= localDelta)
    (hsourceLength : forall i, i ∈ vertices ->
      (sourceRectangle (labelAt i)).rectangle.right -
          (sourceRectangle (labelAt i)).rectangle.left =
        Real.sqrt (sourceDelta / sourceScale))
    (hsourceBase : forall i, i ∈ vertices ->
      (sourceRectangle (labelAt i)).rectangle.base ⊆ domain)
    (hballLocal : forall i, i ∈ vertices ->
      InPointwiseC2BallOn domain localCenter
        (rectangleAt i) (3 * localScale))
    (hrectangle : forall i, i ∈ vertices ->
      rectangleAt i = exactLocalC2GraphRectangle
        (sourceRectangle (labelAt i)) localDelta localScale)
    (pivot : item) :
    ownerClusterMass vertices C.owner
        (firstHitLabelWeight source sourceLabels sourceRectangle sourceDelta
          labelAt)
        pivot <=
      ENNReal.ofReal (2 * (sourceDelta + 6 * localScale)) *
        ENNReal.ofReal
          (Real.sqrt
              (pyzLemma312PackingLambda 100 * localDelta / localScale) +
            Real.sqrt (sourceDelta / sourceScale)) := by
  calc
    ownerClusterMass vertices C.owner
        (firstHitLabelWeight source sourceLabels sourceRectangle sourceDelta
          labelAt)
        pivot <=
      volume
        ((wideSourceFirstHitOwnerContainer (rectangleAt pivot)
          localDelta localScale sourceDelta sourceScale).carrier
            (sourceDelta + 6 * localScale)) :=
      wideSourceFirstHitLabelWeight_ownerClusterMass_le_ownerContainer
        source sourceLabels sourceRectangle vertices labelAt rectangleAt
          domain localCenter globalCenter localDelta localScale referenceScale
            comparisonLambda curvatureRatio centerGap sourceDelta sourceScale
              C hsource hlabelMem hlabelInj hlocalDelta hsourceLength
                hsourceBase hballLocal hrectangle pivot
    _ = ENNReal.ofReal (2 * (sourceDelta + 6 * localScale)) *
        ENNReal.ofReal
          (Real.sqrt
              (pyzLemma312PackingLambda 100 * localDelta / localScale) +
            Real.sqrt (sourceDelta / sourceScale)) := by
      rw [volume_c2GraphRectangle_carrier,
        wideSourceFirstHitOwnerContainer_length]

#print axioms wideSourceFirstHitOwnerContainer
#print axioms wideSourceFirstHitOwnerContainer_length
#print axioms sourceRectangle_carrier_subset_wideSourceFirstHitOwnerContainer
#print axioms wideSourceFirstHitLabelWeight_ownerClusterMass_le_ownerContainer
#print axioms wideSourceFirstHitLabelWeight_ownerClusterMass_le_explicitArea

end

end FamilyStickyCinematicL32Lemma55WideSourceFirstHitLabelWeightOwnerClusterCapV1
