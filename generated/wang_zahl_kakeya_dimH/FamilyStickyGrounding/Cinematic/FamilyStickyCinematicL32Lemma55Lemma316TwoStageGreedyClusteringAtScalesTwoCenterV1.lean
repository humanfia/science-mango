import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1

open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Lemma55SymmetricRectangleComparabilityV1
open FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32Prop41TwoScaleComparabilityCoreV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

universe u

/-!
# Lossless two-centre Lemma 5.5 / Lemma 3.16 clustering

The first stage makes a maximal locally `100`-incomparable pivot family and
records every raw vertex in an owner fibre.  The second stage applies the
proved two-scale neighbour bound to those pivots, using the entire owner-fibre
mass as the greedy weight.

Raw cardinality and mass are exact sums over all pivot clusters.  There is no
claim that raw cardinality is bounded by a constant times the number of final
pivots: such a statement would require an additional bound on the sizes of
the Lemma 5.5 clusters.
-/

/-- Number of raw vertices owned by one pivot. -/
def ownerClusterCard
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha) (owner : alpha -> alpha) (pivot : alpha) : Nat :=
  (vertices.filter fun a => owner a = pivot).card

/-- Arbitrary nonnegative mass carried by one owner fibre. -/
noncomputable def ownerClusterMass
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha) (owner : alpha -> alpha)
    (weight : alpha -> ENNReal) (pivot : alpha) : ENNReal :=
  ∑ a ∈ vertices.filter (fun a => owner a = pivot), weight a

/-- Complete two-stage output, with exact raw cluster partitions. -/
structure CompactC2TwoStageAtScalesTwoCenterClusteringOutcome
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap : Real)
    (weight : alpha -> ENNReal) where
  pivots : Finset alpha
  owner : alpha -> alpha
  selected : Finset alpha
  pivots_subset : pivots ⊆ vertices
  selected_subset_pivots : selected ⊆ pivots
  selected_nonempty : vertices.Nonempty -> selected.Nonempty
  pivots_pairwise_hundred : Set.Pairwise (pivots : Set alpha)
    (fun a b =>
      ¬ symmetricGraphLambdaComparable
        (rectangleAt a).rectangle (rectangleAt b).rectangle
          delta localScale 100)
  selected_pairwise_atScales : Set.Pairwise (selected : Set alpha)
    (fun a b =>
      ¬ compactC2ComparableAtScales rectangleAt domain globalCenter
        delta localScale referenceScale comparisonLambda a b)
  owner_mem : forall a, a ∈ vertices -> owner a ∈ pivots
  owner_comparable : forall a, a ∈ vertices -> owner a = a ∨
    symmetricGraphLambdaComparable
      (rectangleAt (owner a)).rectangle (rectangleAt a).rectangle
        delta localScale 100
  card_partition : vertices.card =
    ∑ b ∈ pivots, ownerClusterCard vertices owner b
  mass_partition : (∑ a ∈ vertices, weight a) =
    ∑ b ∈ pivots, ownerClusterMass vertices owner weight b
  pivot_card_le :
    (pivots.card : ENNReal) <=
      pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        (selected.card : ENNReal)
  raw_mass_le_selected_cluster_mass :
    (∑ a ∈ vertices, weight a) <=
      pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        ∑ b ∈ selected, ownerClusterMass vertices owner weight b

/-- Callback-free two-stage two-scale selection.  The local `100` Pairwise
input of Lemma 3.16 is produced internally by the maximal clustering step. -/
theorem exists_compactC2_twoStage_greedy_clusteringAtScales_twoCenter
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap : Real}
    (weight : alpha -> ENNReal)
    (hdelta : 0 < delta) (hlocal : 0 < localScale)
    (hcomparisonLambda : 100 <= comparisonLambda)
    (hratio : 0 <= curvatureRatio)
    (hscaleRatio :
      3 * localScale + centerGap + 3 * referenceScale <=
        curvatureRatio * localScale)
    (hlength : forall a, a ∈ vertices ->
      (rectangleAt a).rectangle.right -
          (rectangleAt a).rectangle.left =
        Real.sqrt (delta / localScale))
    (hbase : forall a, a ∈ vertices ->
      (rectangleAt a).rectangle.base ⊆ domain)
    (hballLocal : forall a, a ∈ vertices ->
      InPointwiseC2BallOn domain localCenter
        (rectangleAt a) (3 * localScale))
    (hcenterSecond : forall z, z ∈ domain ->
      |localCenter.second z - globalCenter.second z| <= centerGap)
    (hsegmentDomain : forall a, a ∈ vertices ->
      forall b, b ∈ vertices ->
      forall x, x ∈ (rectangleAt a).rectangle.base ->
      forall y, y ∈ (rectangleAt b).rectangle.base ->
        [[x, y]] ⊆ domain) :
    Nonempty (CompactC2TwoStageAtScalesTwoCenterClusteringOutcome
      vertices rectangleAt domain localCenter globalCenter delta localScale
        referenceScale comparisonLambda curvatureRatio centerGap weight) := by
  classical
  obtain ⟨pivots, owner, hpivotsSubset, hpivotsNonempty,
      hpivotsHundred, hownerMem, hownerComparable,
      hcardPartition, hmassPartition⟩ :=
    exists_maximal_pairwise_not_relation_clustering vertices
      (fun a b => symmetricGraphLambdaComparable
        (rectangleAt a).rectangle (rectangleAt b).rectangle
          delta localScale 100)
      ⟨fun _ _ hab => symmetricGraphLambdaComparable_symm hab⟩ weight
  let clusterWeight : alpha -> ENNReal := fun b =>
    ownerClusterMass vertices owner weight b
  obtain ⟨selected, hselectedSubset, hselectedNonempty,
      hselectedPairwise, hpivotCard, hclusterMass⟩ :=
    exists_greedy_compactC2_incomparable_automaticAtScales_twoCenter
      pivots rectangleAt domain localCenter globalCenter clusterWeight
        hdelta hlocal hcomparisonLambda hratio hscaleRatio
      (fun a ha => hlength a (hpivotsSubset ha))
      (fun a ha => hbase a (hpivotsSubset ha))
      (fun a ha => hballLocal a (hpivotsSubset ha))
      hcenterSecond
      (fun a ha b hb => hsegmentDomain a (hpivotsSubset ha)
        b (hpivotsSubset hb))
      hpivotsHundred
  have hrawMass :
      (∑ a ∈ vertices, weight a) <=
        pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          ∑ b ∈ selected, ownerClusterMass vertices owner weight b := by
    calc
      (∑ a ∈ vertices, weight a) =
          ∑ b ∈ pivots, clusterWeight b := by
            simpa only [clusterWeight, ownerClusterMass] using hmassPartition
      _ <= pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          ∑ b ∈ selected, clusterWeight b := hclusterMass
      _ = pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          ∑ b ∈ selected, ownerClusterMass vertices owner weight b := by
            rfl
  exact ⟨{
    pivots := pivots
    owner := owner
    selected := selected
    pivots_subset := hpivotsSubset
    selected_subset_pivots := hselectedSubset
    selected_nonempty := fun hvertices =>
      hselectedNonempty (hpivotsNonempty hvertices)
    pivots_pairwise_hundred := hpivotsHundred
    selected_pairwise_atScales := hselectedPairwise
    owner_mem := hownerMem
    owner_comparable := hownerComparable
    card_partition := by
      simpa only [ownerClusterCard] using hcardPartition
    mass_partition := by
      simpa only [ownerClusterMass] using hmassPartition
    pivot_card_le := hpivotCard
    raw_mass_le_selected_cluster_mass := hrawMass }⟩

#print axioms ownerClusterCard
#print axioms ownerClusterMass
#print axioms CompactC2TwoStageAtScalesTwoCenterClusteringOutcome
#print axioms exists_compactC2_twoStage_greedy_clusteringAtScales_twoCenter

end

end FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
