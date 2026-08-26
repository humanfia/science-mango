import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedCollisionCellExplicitHullPopularFloorUnionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2PopularFibersV1
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedActualShadingInstantiationV1
open FamilyStickyWZ2TranslatedShadingUnionCovarianceV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2TranslatedShadingUnionCopyLossV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
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
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1
open FamilyStickyHierarchyWZ2TranslatedSharedHundredHullVolumeV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Popular WZ2 union endpoint with an explicit shared-hull volume

The preceding popularity endpoint contains the volume of the closed convex
hull of the shared source `100T` shear copies.  The finite-grid shear box
estimate bounds that volume without accepting it as a premise.  This module
performs exactly that monotone substitution, first for an arbitrary shared
source container and then for the selected hierarchy collision cell.

The restricted-mass lower bound and all numerical inputs remain explicit.
-/

/-- Generic finite-shear endpoint in which the shared-hull volume has been
replaced by the explicit coordinate-box volume bound. -/
theorem popularRestricted_halfMass_le_explicitSharedHundredHull_originalUnion
    {kappa : Type*} [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (active : Finset kappa) (X : Set Space)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass : alpha * active.card * cap ≤
      ∑ i ∈ active, restrictedMassReal Y X i)
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily
        (shearReducedShift spacing (siteCount := siteCount))
        (tubeBodyFamily fine.tubes))) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
      (C *
        (shearGridTubeVolumeBound
          (hundredTube shared.container) spacing siteCount /
          popularCarrierFloor alpha cap)) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount)) fine Y) /
          (siteCount : ENNReal)) := by
  have hbase :=
    popularRestricted_halfMass_le_sharedHundredHull_originalUnion
      (htau := ⟨⟨0, hsiteCount⟩⟩)
      (shift := shearReducedShift spacing (siteCount := siteCount))
      fine shared Y active X alpha cap halphaPos hcapPos hmass hKT
  calc
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
        (C *
          (volume
              (translatedSharedHundredHullContainer
                (shearReducedShift spacing (siteCount := siteCount))
                fine shared : Set Space) /
            popularCarrierFloor alpha cap)) *
          (volume
              (indexedTranslatedActualShadingUnion
                (shearReducedShift spacing (siteCount := siteCount)) fine Y) /
            (siteCount : ENNReal)) := by
      simpa only [Fintype.card_fin] using hbase
    _ ≤ (C *
          (shearGridTubeVolumeBound
              (hundredTube shared.container) spacing siteCount /
            popularCarrierFloor alpha cap)) *
          (volume
              (indexedTranslatedActualShadingUnion
                (shearReducedShift spacing (siteCount := siteCount)) fine Y) /
            (siteCount : ENNReal)) := by
      gcongr
      exact volume_translatedSharedHundredHullContainer_le_explicit
        hsiteCount spacing fine shared

/-- Projected-slice form of the generic explicit-hull endpoint. -/
theorem projectedSlice_halfMass_le_explicitSharedHundredHull_originalUnion
    {kappa : Type*} [Fintype kappa]
    {delta : NNReal} [DecidableEq kappa]
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real)
    (fine : UniformTubeFamily delta kappa)
    (shared : SharedHundredSourceContainer fine)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (active : Finset kappa)
    (f : Real → Real) (hf : Measurable f) (X : Set ProjectionSpace)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass : alpha * active.card * cap ≤
      (∫⁻ u in X, projectedActiveMultiplicity Y active f u
        ∂(volume : Measure ProjectionSpace)).toReal)
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily
        (shearReducedShift spacing (siteCount := siteCount))
        (tubeBodyFamily fine.tubes))) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
      (C *
        (shearGridTubeVolumeBound
          (hundredTube shared.container) spacing siteCount /
          popularCarrierFloor alpha cap)) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount)) fine Y) /
          (siteCount : ENNReal)) := by
  apply popularRestricted_halfMass_le_explicitSharedHundredHull_originalUnion
    hsiteCount spacing fine shared Y active (twistedProjection f ⁻¹' X)
      alpha cap halphaPos hcapPos
  · rw [sum_restrictedMassReal_eq_projectedActiveMultiplicity_toReal
      Y active f hf X]
    exact hmass
  · exact hKT

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {spacing : Real} {siteCount gridConstant : Nat}

/-- Selected hierarchy collision-cell specialization.  Katz--Tao and the
shared source container are produced by the existing collision certificate;
the shared hull is bounded by the literal finite-shear coordinate box. -/
theorem selectedHierarchyCollisionCell_popularRestricted_halfMass_le_explicit_originalUnion
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
    (active : Finset
      (SelectedHierarchyCollisionCellIndex H G joint k p a r))
    (X : Set Space)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass : alpha * active.card * cap ≤
      ∑ i ∈ active, restrictedMassReal Y X i) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
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
    popularRestricted_halfMass_le_explicitSharedHundredHull_originalUnion
      hsiteCount spacing
      (selectedHierarchyCollisionCellFamily H G joint k p a r)
      (selectedHierarchyCollisionCell_sharedHundredSourceContainer
        H G joint k p a r)
      Y active X alpha cap halphaPos hcapPos hmass hKT

#print axioms popularRestricted_halfMass_le_explicitSharedHundredHull_originalUnion
#print axioms projectedSlice_halfMass_le_explicitSharedHundredHull_originalUnion
#print axioms selectedHierarchyCollisionCell_popularRestricted_halfMass_le_explicit_originalUnion

end
end FamilyStickyHierarchyWZ2TranslatedCollisionCellExplicitHullPopularFloorUnionV1
