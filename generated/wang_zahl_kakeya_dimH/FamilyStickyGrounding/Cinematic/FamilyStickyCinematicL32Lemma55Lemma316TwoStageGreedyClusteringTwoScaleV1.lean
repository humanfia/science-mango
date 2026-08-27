import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoScaleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringTwoScaleV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoScaleV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoScaleV1

noncomputable section

universe u

/-!
# Two-stage greedy clustering with an independent reference scale

The first maximal `100`-incomparable stage is unchanged and transports raw
mass exactly through owner fibres.  Only the second greedy stage is replaced
by the two-scale Lemma 3.16 theorem.  Consequently no raw Pairwise premise
is needed, while the selected pivots satisfy the literal `AtScales`
relation consumed by the RepoV2 endpoint.

There is deliberately no false raw-cardinality-to-selected-cardinality
field: first-stage owner fibres can have unbounded cardinality.  The honest
transport is the selected cluster-mass inequality below.
-/

structure CompactC2TwoStageGreedyClusteringAtScalesOutcome
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio : Real)
    (weight : alpha -> ENNReal) where
  pivots : Finset alpha
  owner : alpha -> alpha
  selected : Finset alpha
  pivots_subset : pivots ⊆ vertices
  selected_subset_pivots : selected ⊆ pivots
  selected_nonempty : vertices.Nonempty -> selected.Nonempty
  pivots_pairwise_hundred : Set.Pairwise (pivots : Set alpha)
    (fun a b =>
      ¬ compactC2ComparableAt rectangleAt domain center
        delta localScale 100 a b)
  selected_pairwise : Set.Pairwise (selected : Set alpha)
    (fun a b =>
      ¬ compactC2ComparableAtScales rectangleAt domain center
        delta localScale referenceScale comparisonLambda a b)
  owner_mem : forall a, a ∈ vertices -> owner a ∈ pivots
  owner_comparable : forall a, a ∈ vertices -> owner a = a ∨
    compactC2ComparableAt rectangleAt domain center
      delta localScale 100 (owner a) a
  cluster_carrier_subset : forall a, a ∈ vertices ->
    (rectangleAt a).carrier delta ⊆
      (centeredC2GraphRectangleDilation (rectangleAt (owner a)) delta
        localScale (pyzLemma312PackingLambda 100)).carrier
          (pyzLemma312PackingLambda 100 * delta)
  card_partition : vertices.card =
    ∑ b ∈ pivots, (vertices.filter fun a => owner a = b).card
  mass_partition : (∑ a ∈ vertices, weight a) =
    ∑ b ∈ pivots,
      ∑ a ∈ vertices.filter (fun a => owner a = b), weight a
  pivot_card_le : (pivots.card : ENNReal) <=
    pyzClosedNeighbourBound
        (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio) *
      (selected.card : ENNReal)
  raw_mass_le_selected_cluster_mass :
    (∑ a ∈ vertices, weight a) <=
      pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio) *
        ∑ b ∈ selected,
          ∑ a ∈ vertices.filter (fun a => owner a = b), weight a

theorem exists_compactC2_twoStage_greedy_clusteringAtScales
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio : Real}
    (weight : alpha -> ENNReal)
    (hdelta : 0 < delta) (hlocal : 0 < localScale)
    (hcomparisonLambda : 100 <= comparisonLambda)
    (hcurvatureRatio : 0 <= curvatureRatio)
    (hscaleRatio : 3 * (localScale + referenceScale) <=
      curvatureRatio * localScale)
    (hlength : forall a, a ∈ vertices ->
      (rectangleAt a).rectangle.right -
          (rectangleAt a).rectangle.left =
        Real.sqrt (delta / localScale))
    (hbase : forall a, a ∈ vertices ->
      (rectangleAt a).rectangle.base ⊆ domain)
    (hballLocal : forall a, a ∈ vertices ->
      InPointwiseC2BallOn domain center (rectangleAt a) (3 * localScale))
    (hsegmentDomain : forall a, a ∈ vertices ->
      forall b, b ∈ vertices ->
      forall x, x ∈ (rectangleAt a).rectangle.base ->
      forall y, y ∈ (rectangleAt b).rectangle.base ->
        [[x, y]] ⊆ domain) :
    Nonempty (CompactC2TwoStageGreedyClusteringAtScalesOutcome vertices
      rectangleAt domain center delta localScale referenceScale
        comparisonLambda curvatureRatio weight) := by
  classical
  obtain ⟨pivots, owner, hpivotsSubset, hpivotsNonempty,
      hpivotsHundred, hownerMem, hownerComparable,
      hcardPartition, hmassPartition⟩ :=
    exists_maximal_hundred_incomparable_compactC2_clustering
      vertices rectangleAt domain center weight
  let clusterWeight : alpha -> ENNReal := fun b =>
    ∑ a ∈ vertices.filter (fun a => owner a = b), weight a
  have hpivotsHundred' : Set.Pairwise (pivots : Set alpha)
      (fun a b =>
        ¬ compactC2SymmetricGraphLambdaComparableOn
          domain center (rectangleAt a) (rectangleAt b)
            delta localScale 100) := hpivotsHundred
  obtain ⟨selected, hselectedSubset, hselectedNonempty,
      hselectedPairwise, hpivotCard, hclusterMass⟩ :=
    exists_greedy_compactC2_incomparable_automaticAtScales
      pivots rectangleAt domain center clusterWeight hdelta hlocal
        hcomparisonLambda hcurvatureRatio hscaleRatio
      (fun a ha => hlength a (hpivotsSubset ha))
      (fun a ha => hbase a (hpivotsSubset ha))
      (fun a ha => hballLocal a (hpivotsSubset ha))
      (fun a ha b hb => hsegmentDomain a (hpivotsSubset ha)
        b (hpivotsSubset hb))
      hpivotsHundred'
  have hpackingOne : 1 <= pyzLemma312PackingLambda (100 : Real) := by
    linarith [pyzLemma312PackingLambda_ge_hundred (by norm_num :
      (100 : Real) <= 100)]
  have hclusterCarrier : forall a, a ∈ vertices ->
      (rectangleAt a).carrier delta ⊆
        (centeredC2GraphRectangleDilation (rectangleAt (owner a)) delta
          localScale (pyzLemma312PackingLambda 100)).carrier
            (pyzLemma312PackingLambda 100 * delta) := by
    intro a ha
    have hownerPivot := hownerMem a ha
    have hownerVertex := hpivotsSubset hownerPivot
    rcases hownerComparable a ha with hownerEq | hcomparable
    · simpa [hownerEq] using
        (carrier_subset_centeredC2GraphRectangleDilation
          (rectangleAt a) hdelta.le hlocal hpackingOne (hlength a ha))
    · exact carrier_subset_centeredDilation_of_compactC2Comparable
        hdelta hlocal (by norm_num) (hlength (owner a) hownerVertex)
          (hbase (owner a) hownerVertex) (hballLocal (owner a) hownerVertex)
          (hsegmentDomain (owner a) hownerVertex a ha) hcomparable
  have hrawMass :
      (∑ a ∈ vertices, weight a) <=
        pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          ∑ b ∈ selected,
            ∑ a ∈ vertices.filter (fun a => owner a = b), weight a := by
    calc
      (∑ a ∈ vertices, weight a) =
          ∑ b ∈ pivots, clusterWeight b := by
            simpa only [clusterWeight] using hmassPartition
      _ <= pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          ∑ b ∈ selected, clusterWeight b := hclusterMass
      _ = pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          ∑ b ∈ selected,
            ∑ a ∈ vertices.filter (fun a => owner a = b), weight a := by
              rfl
  exact ⟨{
    pivots := pivots
    owner := owner
    selected := selected
    pivots_subset := hpivotsSubset
    selected_subset_pivots := hselectedSubset
    selected_nonempty := fun hvertices =>
      hselectedNonempty (hpivotsNonempty hvertices)
    pivots_pairwise_hundred := by
      simpa only [compactC2ComparableAt] using hpivotsHundred
    selected_pairwise := hselectedPairwise
    owner_mem := hownerMem
    owner_comparable := by
      simpa only [compactC2ComparableAt] using hownerComparable
    cluster_carrier_subset := hclusterCarrier
    card_partition := hcardPartition
    mass_partition := hmassPartition
    pivot_card_le := hpivotCard
    raw_mass_le_selected_cluster_mass := hrawMass }⟩

#print axioms CompactC2TwoStageGreedyClusteringAtScalesOutcome
#print axioms exists_compactC2_twoStage_greedy_clusteringAtScales

end

end FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringTwoScaleV1
