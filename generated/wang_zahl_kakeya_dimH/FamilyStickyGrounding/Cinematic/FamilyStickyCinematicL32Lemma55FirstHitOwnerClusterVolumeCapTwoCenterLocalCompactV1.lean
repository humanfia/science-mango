import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterLocalCompactV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapTwoCenterLocalCompactV1

open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterLocalCompactV1

noncomputable section

universe u

/-!
# First-hit owner mass cap for the two-centre local-compact selector

The local compact-C2 first stage supplies the single pivot-centred carrier
missing from the weaker centre-free two-centre outcome.  First-hit
measurability and disjointness then give the same explicit area cap as in the
single-centre route, while the selected Pairwise field remains based at the
independent global centre.
-/

theorem firstHitY2_ownerClusterMass_le_ownerDilation_twoCenterLocalCompact
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (vertices : Finset index)
    (rectangleAt : index -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap : Real)
    (C : CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome vertices
      rectangleAt domain localCenter globalCenter delta localScale
        referenceScale comparisonLambda curvatureRatio centerGap
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i)))
    (hsource : MeasurableSet source) (pivot : index) :
    ownerClusterMass vertices C.owner
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i))
        pivot <=
      volume
        ((centeredC2GraphRectangleDilation (rectangleAt pivot) delta
          localScale (pyzLemma312PackingLambda 100)).carrier
            (pyzLemma312PackingLambda 100 * delta)) := by
  apply ownerClusterMass_measure_le_target volume vertices C.owner
    (firstHitFineRectangleY2 source vertices rectangleAt delta) pivot
  · intro i _hi
    exact measurableSet_firstHitFineRectangleY2
      source vertices rectangleAt delta hsource i
  · exact firstHitFineRectangleY2_pairwiseDisjoint
      source vertices rectangleAt delta
  · intro i hi howner
    apply (firstHitFineRectangleY2_subset_carrier
      source vertices rectangleAt delta i).trans
    simpa only [howner] using C.cluster_carrier_subset i hi

theorem firstHitY2_ownerClusterMass_le_explicitDilationArea_twoCenterLocalCompact
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (vertices : Finset index)
    (rectangleAt : index -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap : Real)
    (C : CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome vertices
      rectangleAt domain localCenter globalCenter delta localScale
        referenceScale comparisonLambda curvatureRatio centerGap
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i)))
    (hsource : MeasurableSet source) (pivot : index) :
    ownerClusterMass vertices C.owner
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i))
        pivot <=
      ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
        ENNReal.ofReal
          (Real.sqrt
            (pyzLemma312PackingLambda 100 * delta / localScale)) := by
  calc
    ownerClusterMass vertices C.owner
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i))
        pivot <=
      volume
        ((centeredC2GraphRectangleDilation (rectangleAt pivot) delta
          localScale (pyzLemma312PackingLambda 100)).carrier
            (pyzLemma312PackingLambda 100 * delta)) :=
      firstHitY2_ownerClusterMass_le_ownerDilation_twoCenterLocalCompact
        source vertices rectangleAt domain localCenter globalCenter delta
          localScale referenceScale comparisonLambda curvatureRatio centerGap
          C hsource pivot
    _ = ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
        ENNReal.ofReal
          (Real.sqrt
            (pyzLemma312PackingLambda 100 * delta / localScale)) := by
      rw [volume_c2GraphRectangle_carrier,
        centeredC2GraphRectangleDilation_length]

/-- Exact first-hit mass and the two-stage mass transport give the per-fibre
source-volume bound required by the all-fibres top. -/
theorem volume_source_le_neighbourBound_mul_selectedCard_mul_dilationArea_twoCenterLocalCompact
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (vertices : Finset index)
    (rectangleAt : index -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap : Real)
    (C : CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome vertices
      rectangleAt domain localCenter globalCenter delta localScale
        referenceScale comparisonLambda curvatureRatio centerGap
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i)))
    (hsource : MeasurableSet source)
    (hcover : forall x, x ∈ source ->
      exists i, i ∈ vertices ∧ x ∈ (rectangleAt i).carrier delta) :
    volume source <=
      pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        (C.selected.card : ENNReal) *
        (ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
          ENNReal.ofReal
            (Real.sqrt
              (pyzLemma312PackingLambda 100 * delta / localScale))) := by
  let area : ENNReal :=
    ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
      ENNReal.ofReal
        (Real.sqrt
          (pyzLemma312PackingLambda 100 * delta / localScale))
  have hmass :
      (∑ i ∈ vertices,
        volume (firstHitFineRectangleY2
          source vertices rectangleAt delta i)) = volume source :=
    sum_measure_firstHitFineRectangleY2_eq_source volume source vertices
      rectangleAt delta hsource hcover
  have hcluster : forall b, b ∈ C.selected ->
      ownerClusterMass vertices C.owner
        (fun i => volume (firstHitFineRectangleY2
          source vertices rectangleAt delta i)) b <= area := by
    intro b _hb
    simpa only [area] using
      (firstHitY2_ownerClusterMass_le_explicitDilationArea_twoCenterLocalCompact
        source vertices rectangleAt domain localCenter globalCenter delta
          localScale referenceScale comparisonLambda curvatureRatio centerGap
          C hsource b)
  calc
    volume source =
        ∑ i ∈ vertices,
          volume (firstHitFineRectangleY2
            source vertices rectangleAt delta i) := hmass.symm
    _ <= pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        ∑ b ∈ C.selected,
          ownerClusterMass vertices C.owner
            (fun i => volume (firstHitFineRectangleY2
              source vertices rectangleAt delta i)) b :=
      C.raw_mass_le_selected_cluster_mass
    _ <= pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        ∑ _b ∈ C.selected, area := by
      gcongr with b hb
      exact hcluster b hb
    _ = pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        (C.selected.card : ENNReal) * area := by
      simp [nsmul_eq_mul, mul_assoc]
    _ = pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        (C.selected.card : ENNReal) *
        (ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
          ENNReal.ofReal
            (Real.sqrt
              (pyzLemma312PackingLambda 100 * delta / localScale))) := by
      rfl

#print axioms firstHitY2_ownerClusterMass_le_ownerDilation_twoCenterLocalCompact
#print axioms firstHitY2_ownerClusterMass_le_explicitDilationArea_twoCenterLocalCompact
#print axioms volume_source_le_neighbourBound_mul_selectedCard_mul_dilationArea_twoCenterLocalCompact

end

end FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapTwoCenterLocalCompactV1
