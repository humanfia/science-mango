import FamilyStickyGrounding.FamilyStickyWZ2ProjectedShadedUnionMassV1
import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellExplicitHullPopularFloorUnionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedCollisionCellProjectedShadedUnionExplicitHullV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
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
open FamilyStickyHierarchyWZ2TranslatedCollisionCellKatzTaoV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellExplicitHullPopularFloorUnionV1
open FamilyStickyWZ2ProjectedShadedUnionMassV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Explicit-hull WZ2 endpoint from full projected shading mass

Restrict the projected multiplicity to the literal projection of the full
shaded union and take every source index active.  The resulting restricted
integral is exactly the complete source shading mass.  Feeding this identity
into the explicit shared-hull popularity endpoint leaves only the transparent
scalar shading-mass lower bound, Katz--Tao, and the geometric numerical data.
-/

/-- Generic finite-shear endpoint whose sole mass input is a scalar lower
bound for the complete source shading mass. -/
theorem projectedShadedUnion_halfMass_le_explicitSharedHundredHull_originalUnion
    {kappa : Type*} [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (f : Real → Real) (hf : Measurable f)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass : alpha * Fintype.card kappa * cap ≤ Y.shadingMass.toReal)
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily
        (shearReducedShift spacing (siteCount := siteCount))
        (tubeBodyFamily fine.tubes))) :
    ENNReal.ofReal (alpha / 2 * Fintype.card kappa * cap) ≤
      (C *
        (shearGridTubeVolumeBound
          (hundredTube shared.container) spacing siteCount /
          popularCarrierFloor alpha cap)) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount)) fine Y) /
          (siteCount : ENNReal)) := by
  have hprojected :=
    projectedShadedUnion_massLower Y f hf alpha cap hmass
  simpa only [Finset.card_univ] using
    (projectedSlice_halfMass_le_explicitSharedHundredHull_originalUnion
      hsiteCount spacing fine shared Y (Finset.univ : Finset kappa)
      f hf (twistedProjection f '' Y.shadedUnion)
      alpha cap halphaPos hcapPos hprojected hKT)

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {spacing : Real} {siteCount gridConstant : Nat}

/-- Selected hierarchy collision-cell specialization.  The collision
certificate supplies Katz--Tao, while the only mass hypothesis is the scalar
lower bound for the full source shading mass. -/
theorem selectedHierarchyCollisionCell_projectedShadedUnion_halfMass_le_explicit_originalUnion
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
    (Y : Shading
      (tubeBodyFamily
        (selectedHierarchyCollisionCellFamily H G joint k p a r).tubes))
    (f : Real → Real) (hf : Measurable f)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass :
      alpha *
          Fintype.card
            (SelectedHierarchyCollisionCellIndex H G joint k p a r) *
          cap ≤
        Y.shadingMass.toReal) :
    ENNReal.ofReal
        (alpha / 2 *
          Fintype.card
            (SelectedHierarchyCollisionCellIndex H G joint k p a r) *
          cap) ≤
      ((16 *
          ((gridConstant * commonHundredNeighbourPackingConstant : Nat) :
            ENNReal)) *
        (shearGridTubeVolumeBound
            (hundredTube
              (selectedHierarchyCollisionCell_sharedHundredSourceContainer
                H G joint k p a r).container)
            spacing siteCount /
          popularCarrierFloor alpha cap)) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount))
              (selectedHierarchyCollisionCellFamily H G joint k p a r) Y) /
          (siteCount : ENNReal)) := by
  have hKT :=
    selectedHierarchyCollisionCell_fullTranslatedFamily_isKatzTao
      grid joint wz k p hp a r baseD rho hspacing hrho source hselected
        hcluster
  exact
    projectedShadedUnion_halfMass_le_explicitSharedHundredHull_originalUnion
      hsiteCount spacing
      (selectedHierarchyCollisionCellFamily H G joint k p a r)
      (selectedHierarchyCollisionCell_sharedHundredSourceContainer
        H G joint k p a r)
      Y f hf alpha cap halphaPos hcapPos hmass hKT

#print axioms projectedShadedUnion_halfMass_le_explicitSharedHundredHull_originalUnion
#print axioms selectedHierarchyCollisionCell_projectedShadedUnion_halfMass_le_explicit_originalUnion

end
end FamilyStickyHierarchyWZ2TranslatedCollisionCellProjectedShadedUnionExplicitHullV1
