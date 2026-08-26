import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellUniformDensityExplicitHullV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyWZ2CollisionCellShadingRestrictionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedShadingUnionCopyLossV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyWZ2FixedGridConstantEndpointV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellUniformDensityExplicitHullV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Honest restriction of a hierarchy-level shading to a collision cell

A selected hierarchy collision cell is literally a subtype of the level-`k`
index family.  Its tube at `i` is definitionally the level tube at `i.val`.
Consequently any genuine shading on the complete level family restricts to a
genuine shading on the collision cell without a body-identification premise.

Restriction alone does not preserve density.  The quantitative bridge below
therefore accepts the honest missing selection datum: the level shading mass
is at most `loss` times the mass retained in this literal cell.  The matching
family-volume comparison is proved automatically from subtype inclusion.
No collision-cell density target is accepted as a premise.
-/

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}

/-- The canonical subtype map from a selected collision cell to its actual
level-`k` hierarchy index family. -/
def selectedHierarchyCollisionCellIndexEmbedding
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k)) :
    SelectedHierarchyCollisionCellIndex H G joint k p a r ↪ Index k.1 :=
  Function.Embedding.subtype _

@[simp]
theorem selectedHierarchyCollisionCellIndexEmbedding_apply
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (i : SelectedHierarchyCollisionCellIndex H G joint k p a r) :
    selectedHierarchyCollisionCellIndexEmbedding joint k p a r i = i.1 :=
  rfl

/-- The collision-cell tube body at a subtype index is literally the
corresponding level-`k` hierarchy tube body. -/
@[simp]
theorem selectedHierarchyCollisionCell_body_eq_levelBody
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (i : SelectedHierarchyCollisionCellIndex H G joint k p a r) :
    tubeBodyFamily
        (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes i =
      (H.effectiveFamily k.1).bodyFamily i.1 :=
  rfl

/-- Restrict a genuine level-`k` hierarchy shading along the canonical
collision-cell subtype embedding. -/
def selectedHierarchyCollisionCellShading
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading (H.effectiveFamily k.1).bodyFamily) :
    Shading
      (tubeBodyFamily
        (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes) where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := by
    simpa only [selectedHierarchyCollisionCell_body_eq_levelBody] using
      Y.carrier_subset i.1

@[simp]
theorem selectedHierarchyCollisionCellShading_carrier
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading (H.effectiveFamily k.1).bodyFamily)
    (i : SelectedHierarchyCollisionCellIndex H G joint k p a r) :
    (selectedHierarchyCollisionCellShading joint k p a r Y).carrier i =
      Y.carrier i.1 :=
  rfl

/-- Exact subtype sum for the mass retained in the collision cell. -/
theorem selectedHierarchyCollisionCellShading_shadingMass
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading (H.effectiveFamily k.1).bodyFamily) :
    (selectedHierarchyCollisionCellShading joint k p a r Y).shadingMass =
      ∑ i : SelectedHierarchyCollisionCellIndex H G joint k p a r,
        volume (Y.carrier i.1) := by
  rfl

/-- Exact subtype sum for the collision-cell family-volume denominator. -/
theorem selectedHierarchyCollisionCell_familyVolume
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k)) :
    familyVolume
        (tubeBodyFamily
          (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes) =
      ∑ i : SelectedHierarchyCollisionCellIndex H G joint k p a r,
        volume ((H.effectiveFamily k.1).bodyFamily i.1 : Set Space) := by
  simp only [familyVolume, selectedHierarchyCollisionCell_body_eq_levelBody]

/-- The exact subtype denominator is no larger than the complete level-`k`
family denominator. -/
theorem selectedHierarchyCollisionCell_familyVolume_le_levelFamilyVolume
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k)) :
    familyVolume
        (tubeBodyFamily
          (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes) ≤
      familyVolume (H.effectiveFamily k.1).bodyFamily := by
  classical
  rw [selectedHierarchyCollisionCell_familyVolume joint k p a r,
    familyVolume]
  calc
    (∑ i : SelectedHierarchyCollisionCellIndex H G joint k p a r,
        volume ((H.effectiveFamily k.1).bodyFamily i.1 : Set Space)) =
        ∑ i ∈ candidateCollisionFinset
            (hierarchyCollisionGrid H G joint k p) a
            ((joint.output.layerOutput k).omega r),
          volume ((H.effectiveFamily k.1).bodyFamily i : Set Space) := by
      symm
      exact Finset.sum_subtype _ (fun _i => Iff.rfl) _
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Index k.1)),
          volume ((H.effectiveFamily k.1).bodyFamily i : Set Space) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ i : Index k.1,
          volume ((H.effectiveFamily k.1).bodyFamily i : Set Space) := by simp

/-- An explicit mass-retention loss and the automatic denominator inclusion
transport level density to the literal collision-cell restriction. -/
theorem levelDensity_div_loss_le_selectedHierarchyCollisionCellShading_density
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading (H.effectiveFamily k.1).bodyFamily)
    (loss : ENNReal)
    (hretained : Y.shadingMass ≤
      loss *
        (selectedHierarchyCollisionCellShading joint k p a r Y).shadingMass) :
    Y.shadingDensity / loss ≤
      (selectedHierarchyCollisionCellShading joint k p a r Y).shadingDensity := by
  let Z := selectedHierarchyCollisionCellShading joint k p a r Y
  have hfamily :
      familyVolume
          (tubeBodyFamily
            (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes) ≤
        familyVolume (H.effectiveFamily k.1).bodyFamily :=
    selectedHierarchyCollisionCell_familyVolume_le_levelFamilyVolume
      joint k p a r
  have hsource : Y.shadingDensity ≤ loss * Z.shadingDensity := by
    by_cases hzero : familyVolume (H.effectiveFamily k.1).bodyFamily = 0
    · have hmass : Y.shadingMass = 0 :=
        nonpos_iff_eq_zero.mp
          (Y.shadingMass_le_familyVolume.trans_eq hzero)
      simp [Shading.shadingDensity, hzero, hmass]
    · rw [← ENNReal.mul_le_mul_iff_right hzero
        (familyVolume_ne_top (H.effectiveFamily k.1).bodyFamily)]
      calc
        familyVolume (H.effectiveFamily k.1).bodyFamily *
            Y.shadingDensity = Y.shadingMass := by
          rw [mul_comm, shadingDensity_mul_familyVolume]
        _ ≤ loss * Z.shadingMass := hretained
        _ = loss *
            (Z.shadingDensity *
              familyVolume
                (tubeBodyFamily
                  (selectedHierarchyCollisionCellFamily
                    H G joint k p a r).tubes)) := by
          rw [shadingDensity_mul_familyVolume]
        _ ≤ loss *
            (Z.shadingDensity *
              familyVolume (H.effectiveFamily k.1).bodyFamily) := by
          gcongr
        _ = familyVolume (H.effectiveFamily k.1).bodyFamily *
            (loss * Z.shadingDensity) := by ac_rfl
  exact ENNReal.div_le_of_le_mul' hsource

/-- Loss-aware source density plus retained mass yields the absolute density
lower bound required by the uniform-density endpoint. -/
theorem ofReal_le_selectedHierarchyCollisionCellShading_density_of_retainedMass
    (joint : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (Y : Shading (H.effectiveFamily k.1).bodyFamily)
    (alpha : Real) (loss : ENNReal)
    (hlossZero : loss ≠ 0) (hlossTop : loss ≠ ∞)
    (hretained : Y.shadingMass ≤
      loss *
        (selectedHierarchyCollisionCellShading joint k p a r Y).shadingMass)
    (hsourceDensity : ENNReal.ofReal alpha * loss ≤ Y.shadingDensity) :
    ENNReal.ofReal alpha ≤
      (selectedHierarchyCollisionCellShading joint k p a r Y).shadingDensity := by
  have htransport :
      Y.shadingDensity ≤
        loss *
          (selectedHierarchyCollisionCellShading
            joint k p a r Y).shadingDensity := by
    have hdiv :=
      levelDensity_div_loss_le_selectedHierarchyCollisionCellShading_density
        joint k p a r Y loss hretained
    simpa only [mul_comm] using
      (ENNReal.div_le_iff hlossZero hlossTop).mp hdiv
  apply (ENNReal.mul_le_mul_iff_left hlossZero hlossTop).mp
  simpa only [mul_comm] using hsourceDensity.trans htransport

variable {spacing : Real} {siteCount gridConstant : Nat}

/-- Selected WZ2 endpoint for the literal restriction of a level shading.
The downstream density callback is replaced by explicit source-density and
cell mass-retention comparisons. -/
theorem selectedHierarchyCollisionCell_levelShading_uniformDensity_halfMass_le_explicit_originalUnion
    (grid : FixedShearCopyGridCertificate siteCount gridConstant)
    (joint : HierarchyJointRandomMotionCertificate H G)
    (wz : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate (hierarchyCollisionGrid H G joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 ≤ rho)
    (source : Finset
      (SelectedHierarchyCollisionCellIndex H G joint k p a r))
    (hselected :
      (Finset.univ : Finset
        (SelectedHierarchyCollisionCellIndex H G joint k p a r)) ⊆
      fixedVerticalChartIndices
        (selectedHierarchyCollisionCellFamily H G joint k p a r) source)
    (hcluster : ∀ l,
      |tubeGraphD
          ((selectedHierarchyCollisionCellFamily H G joint k p a r).tubes l) -
        baseD| ≤ rho)
    (hsiteCount : 0 < siteCount)
    (Y : Shading (H.effectiveFamily k.1).bodyFamily)
    (f : Real → Real) (hf : Measurable f)
    (alpha : Real) (halphaPos : 0 < alpha)
    (loss : ENNReal) (hlossZero : loss ≠ 0) (hlossTop : loss ≠ ∞)
    (hretained : Y.shadingMass ≤
      loss *
        (selectedHierarchyCollisionCellShading joint k p a r Y).shadingMass)
    (hsourceDensity : ENNReal.ofReal alpha * loss ≤ Y.shadingDensity) :
    ENNReal.ofReal
        (alpha / 2 *
          Fintype.card
            (SelectedHierarchyCollisionCellIndex H G joint k p a r) *
          ((H.effectiveRadius k.1 : Real) ^ 2 / 2)) ≤
      ((16 *
          ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
            ENNReal)) *
        (shearGridTubeVolumeBound
            (hundredTube
              (selectedHierarchyCollisionCell_sharedHundredSourceContainer
                H G joint k p a r).container)
            spacing siteCount /
          popularCarrierFloor alpha
            ((H.effectiveRadius k.1 : Real) ^ 2 / 2))) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount))
              (selectedHierarchyCollisionCellFamily H G joint k p a r)
              (selectedHierarchyCollisionCellShading joint k p a r Y)) /
          (siteCount : ENNReal)) := by
  have hdensity :=
    ofReal_le_selectedHierarchyCollisionCellShading_density_of_retainedMass
      joint k p a r Y alpha loss hlossZero hlossTop hretained hsourceDensity
  exact
    selectedHierarchyCollisionCell_uniformDensity_projectedShadedUnion_halfMass_le_explicit_originalUnion
      grid joint wz k p hp a r baseD rho hspacing hrho source hselected
      hcluster hsiteCount
      (selectedHierarchyCollisionCellShading joint k p a r Y)
      f hf alpha halphaPos hdensity

#print axioms selectedHierarchyCollisionCell_body_eq_levelBody
#print axioms selectedHierarchyCollisionCellShading
#print axioms selectedHierarchyCollisionCellShading_shadingMass
#print axioms selectedHierarchyCollisionCell_familyVolume
#print axioms selectedHierarchyCollisionCell_familyVolume_le_levelFamilyVolume
#print axioms levelDensity_div_loss_le_selectedHierarchyCollisionCellShading_density
#print axioms ofReal_le_selectedHierarchyCollisionCellShading_density_of_retainedMass
#print axioms selectedHierarchyCollisionCell_levelShading_uniformDensity_halfMass_le_explicit_originalUnion

end
end FamilyStickyHierarchyWZ2CollisionCellShadingRestrictionV1
