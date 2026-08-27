import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterLocalCompactV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1

noncomputable section

universe u

/-!
# Two-centre clustering with an honest local compact-C2 owner container

The original two-centre selector deliberately used the centre-free
`symmetricGraphLambdaComparable` relation in its first stage.  That is enough
for cardinality transport, but its arbitrary graph witness does not put an
entire owner fibre in one pivot-centred rectangle.  The first-hit mass cap
therefore cannot be recovered from that output alone.

Here the first stage instead uses compact-C2 comparability around the local
centre.  The second stage still uses the independent global centre and the
two-scale relation.  Thus the final selected family has exactly the global
AtScales Pairwise property needed by the counting endpoint, while every raw
owner fibre has a literal local pivot-centred container.
-/

/-- Two-centre greedy selection when the input is `100`-incomparable for the
local compact-C2 relation. -/
theorem exists_greedy_compactC2_incomparable_automaticAtScales_twoCenter_of_localCompactHundred
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
        [[x, y]] ⊆ domain)
    (hHundredIncomparable : Set.Pairwise (vertices : Set alpha)
      (fun a b =>
        ¬ compactC2ComparableAt rectangleAt domain localCenter
          delta localScale 100 a b)) :
    exists selected : Finset alpha,
      selected ⊆ vertices ∧
      (vertices.Nonempty -> selected.Nonempty) ∧
      Set.Pairwise (selected : Set alpha)
        (fun a b =>
          ¬ compactC2ComparableAtScales rectangleAt domain globalCenter
            delta localScale referenceScale comparisonLambda a b) ∧
      (vertices.card : ENNReal) <=
        pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          (selected.card : ENNReal) ∧
      (∑ a ∈ vertices, weight a) <=
        pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          ∑ a ∈ selected, weight a := by
  classical
  let packingLambda := pyzLemma312TwoScalePackingLambda
    comparisonLambda curvatureRatio
  have hcomparisonOne : 1 <= comparisonLambda := by linarith
  have hpackingHundred : 100 <= packingLambda :=
    pyzLemma312TwoScalePackingLambda_ge_hundred
      hcomparisonLambda hratio
  have hpackingOne : 1 <= packingLambda := by linarith
  apply exists_greedy_pairwise_not_relation vertices
    (compactC2ComparableAtScales rectangleAt domain globalCenter
      delta localScale referenceScale comparisonLambda)
    compactC2ComparableAtScales_symm weight
    (pyzClosedNeighbourBound packingLambda)
  intro a ha
  let neighbour := vertices.filter (fun b =>
    b = a ∨ compactC2ComparableAtScales rectangleAt domain globalCenter
      delta localScale referenceScale comparisonLambda a b)
  let container := centeredC2GraphRectangleDilation
    (rectangleAt a) delta localScale packingLambda
  have hpacked :=
    card_le_of_pyz_rectangle_geometry_of_mem_common_c2BallOn
      neighbour rectangleAt container localCenter domain hdelta hlocal
        hpackingHundred
      (fun i hi => hlength i (Finset.filter_subset _ _ hi))
      (centeredC2GraphRectangleDilation_length
        (rectangleAt a) delta localScale packingLambda)
      (fun b hb => by
        have hbData := Finset.mem_filter.mp hb
        rcases hbData.2 with hba | hcomparable
        · subst b
          exact carrier_subset_centeredC2GraphRectangleDilation
            (rectangleAt a) hdelta.le hlocal hpackingOne (hlength a ha)
        · exact
            carrier_subset_centeredDilation_of_compactC2ComparableAtScales_twoCenter
              hdelta hlocal hcomparisonOne hratio hscaleRatio
              (hlength a ha) (hbase a ha) (hballLocal a ha)
              hcenterSecond (hsegmentDomain a ha b hbData.1) hcomparable)
      (fun i hi => hbase i (Finset.filter_subset _ _ hi))
      (fun i hi => hballLocal i (Finset.filter_subset _ _ hi))
      (centeredC2GraphRectangleDilation_mem_c2BallOn (hballLocal a ha))
      (fun i hi j hj hij => by
        have hiVertices : i ∈ vertices := Finset.filter_subset _ _ hi
        have hjVertices : j ∈ vertices := Finset.filter_subset _ _ hj
        have hnotCompact :=
          hHundredIncomparable hiVertices hjVertices hij
        intro hleft
        exact hnotCompact
          (compactC2SymmetricGraphLambdaComparableOn_of_left
            (hballLocal i hiVertices) hleft))
  simpa [neighbour, packingLambda, pyzClosedNeighbourBound] using hpacked

/-- The full two-stage output, with both the global AtScales Pairwise field
and the local owner-container field. -/
structure CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome
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
  pivots_pairwise_hundred_local : Set.Pairwise (pivots : Set alpha)
    (fun a b =>
      ¬ compactC2ComparableAt rectangleAt domain localCenter
        delta localScale 100 a b)
  selected_pairwise_atScales : Set.Pairwise (selected : Set alpha)
    (fun a b =>
      ¬ compactC2ComparableAtScales rectangleAt domain globalCenter
        delta localScale referenceScale comparisonLambda a b)
  owner_mem : forall a, a ∈ vertices -> owner a ∈ pivots
  owner_comparable_local : forall a, a ∈ vertices -> owner a = a ∨
    compactC2ComparableAt rectangleAt domain localCenter
      delta localScale 100 (owner a) a
  cluster_carrier_subset : forall a, a ∈ vertices ->
    (rectangleAt a).carrier delta ⊆
      (centeredC2GraphRectangleDilation (rectangleAt (owner a)) delta
        localScale (pyzLemma312PackingLambda 100)).carrier
          (pyzLemma312PackingLambda 100 * delta)
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

/-- Callback-free local-compact/global-AtScales two-stage clustering. -/
theorem exists_compactC2_twoStage_greedy_clusteringAtScales_twoCenter_localCompact
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
    Nonempty (CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome
      vertices rectangleAt domain localCenter globalCenter delta localScale
        referenceScale comparisonLambda curvatureRatio centerGap weight) := by
  classical
  obtain ⟨pivots, owner, hpivotsSubset, hpivotsNonempty,
      hpivotsHundred, hownerMem, hownerComparable,
      hcardPartition, hmassPartition⟩ :=
    exists_maximal_pairwise_not_relation_clustering vertices
      (compactC2ComparableAt rectangleAt domain localCenter
        delta localScale 100)
      compactC2ComparableAt_symm weight
  let clusterWeight : alpha -> ENNReal := fun b =>
    ownerClusterMass vertices owner weight b
  obtain ⟨selected, hselectedSubset, hselectedNonempty,
      hselectedPairwise, hpivotCard, hclusterMass⟩ :=
    exists_greedy_compactC2_incomparable_automaticAtScales_twoCenter_of_localCompactHundred
      pivots rectangleAt domain localCenter globalCenter clusterWeight
        hdelta hlocal hcomparisonLambda hratio hscaleRatio
      (fun a ha => hlength a (hpivotsSubset ha))
      (fun a ha => hbase a (hpivotsSubset ha))
      (fun a ha => hballLocal a (hpivotsSubset ha))
      hcenterSecond
      (fun a ha b hb => hsegmentDomain a (hpivotsSubset ha)
        b (hpivotsSubset hb))
      hpivotsHundred
  have hpackingOne : 1 <= pyzLemma312PackingLambda (100 : Real) := by
    have hpackingHundred :
        100 <= pyzLemma312PackingLambda (100 : Real) :=
      pyzLemma312PackingLambda_ge_hundred (by norm_num)
    linarith
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
          (hbase (owner a) hownerVertex)
          (hballLocal (owner a) hownerVertex)
          (hsegmentDomain (owner a) hownerVertex a ha) hcomparable
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
    pivots_pairwise_hundred_local := hpivotsHundred
    selected_pairwise_atScales := hselectedPairwise
    owner_mem := hownerMem
    owner_comparable_local := hownerComparable
    cluster_carrier_subset := hclusterCarrier
    card_partition := by
      simpa only [ownerClusterCard] using hcardPartition
    mass_partition := by
      simpa only [ownerClusterMass] using hmassPartition
    pivot_card_le := hpivotCard
    raw_mass_le_selected_cluster_mass := hrawMass }⟩

#print axioms exists_greedy_compactC2_incomparable_automaticAtScales_twoCenter_of_localCompactHundred
#print axioms CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome
#print axioms exists_compactC2_twoStage_greedy_clusteringAtScales_twoCenter_localCompact

end

end FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterLocalCompactV1
