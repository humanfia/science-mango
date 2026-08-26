import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellProjectedShadedUnionExplicitHullV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyWZ2TranslatedCollisionCellUniformDensityExplicitHullV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
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
open FamilyStickyHierarchyWZ2TranslatedCollisionCellProjectedShadedUnionExplicitHullV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Uniform density supplies the explicit-hull WZ2 mass input

Every radius-`delta` tube with `delta <= 1/2` has volume at least
`delta^2 / 2`.  Summing over a finite uniform family gives the corresponding
cardinality lower bound for `familyVolume`.  Multiplication by an honest
lower bound for `shadingDensity`, followed by the exact identity
`shadingDensity * familyVolume = shadingMass`, produces the real scalar mass
input used by the projected-shaded-union endpoint.

No shading-mass inequality is accepted as a premise.
-/

/-- The summed volume of a finite uniform radius-`radius` tube family is at
least its cardinality times `radius^2 / 2`. -/
theorem card_mul_half_sq_le_tubeBodyFamily_familyVolume
    {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
    {radius : NNReal} (hradiusHalf : radius ≤ (2 : NNReal)⁻¹)
    (fine : UniformTubeFamily radius kappa) :
    (Fintype.card kappa : ENNReal) * ((radius : ENNReal) ^ 2 / 2) ≤
      familyVolume (tubeBodyFamily fine.tubes) := by
  rw [familyVolume]
  calc
    (Fintype.card kappa : ENNReal) * ((radius : ENNReal) ^ 2 / 2) =
        ∑ _i : kappa, (radius : ENNReal) ^ 2 / 2 := by simp
    _ ≤ ∑ i : kappa,
          volume (tubeBodyFamily fine.tubes i : Set Space) := by
      exact Finset.sum_le_sum fun i _hi => by
        simpa [tubeBodyFamily, Tube.coe_body] using
          (fine.tubes i).half_sq_le_volume_of_le_half hradiusHalf

/-- An honest lower bound for the average shading density yields the exact
real mass scale consumed downstream.  Finiteness comes from the finite convex
family, not from an additional hypothesis. -/
theorem densityLower_mul_card_half_sq_le_shadingMass_toReal
    {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
    {radius : NNReal} (hradiusHalf : radius ≤ (2 : NNReal)⁻¹)
    (fine : UniformTubeFamily radius kappa)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (alpha : Real) (halpha0 : 0 ≤ alpha)
    (hdensity : ENNReal.ofReal alpha ≤ Y.shadingDensity) :
    alpha * Fintype.card kappa * ((radius : Real) ^ 2 / 2) ≤
      Y.shadingMass.toReal := by
  have hmassENN :
      ENNReal.ofReal alpha *
          ((Fintype.card kappa : ENNReal) *
            ((radius : ENNReal) ^ 2 / 2)) ≤
        Y.shadingMass := by
    calc
      ENNReal.ofReal alpha *
          ((Fintype.card kappa : ENNReal) *
            ((radius : ENNReal) ^ 2 / 2)) ≤
          Y.shadingDensity *
            familyVolume (tubeBodyFamily fine.tubes) :=
        mul_le_mul' hdensity
          (card_mul_half_sq_le_tubeBodyFamily_familyVolume
            hradiusHalf fine)
      _ = Y.shadingMass := shadingDensity_mul_familyVolume Y
  have hreal := ENNReal.toReal_mono Y.shadingMass_lt_top.ne hmassENN
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal halpha0,
    ENNReal.toReal_natCast, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.coe_toReal, ENNReal.toReal_ofNat, mul_assoc] using hreal

/-- Generic finite-shear explicit-hull endpoint in which the scalar shading
mass premise is automatically produced from uniform tube volume and a genuine
shading-density lower bound. -/
theorem uniformDensity_projectedShadedUnion_halfMass_le_explicitSharedHundredHull_originalUnion
    {kappa : Type*} [Fintype kappa]
    {radius : NNReal} [DecidableEq kappa]
    (hradiusHalf : radius ≤ (2 : NNReal)⁻¹) (hradiusPos : 0 < radius)
    {siteCount : Nat} (hsiteCount : 0 < siteCount) (spacing : Real)
    (fine : UniformTubeFamily radius kappa)
    (shared : SharedHundredSourceContainer fine)
    (Y : Shading (tubeBodyFamily fine.tubes))
    (f : Real → Real) (hf : Measurable f)
    (alpha : Real) (halphaPos : 0 < alpha)
    (hdensity : ENNReal.ofReal alpha ≤ Y.shadingDensity)
    {C : ENNReal}
    (hKT : IsKatzTao C
      (indexedTranslatedBodyFamily
        (shearReducedShift spacing (siteCount := siteCount))
        (tubeBodyFamily fine.tubes))) :
    ENNReal.ofReal
        (alpha / 2 * Fintype.card kappa *
          ((radius : Real) ^ 2 / 2)) ≤
      (C *
        (shearGridTubeVolumeBound
          (hundredTube shared.container) spacing siteCount /
          popularCarrierFloor alpha ((radius : Real) ^ 2 / 2))) *
        (volume
            (indexedTranslatedActualShadingUnion
              (shearReducedShift spacing (siteCount := siteCount)) fine Y) /
          (siteCount : ENNReal)) := by
  have hradiusReal : 0 < (radius : Real) := NNReal.coe_pos.mpr hradiusPos
  have hcapPos : 0 < (radius : Real) ^ 2 / 2 := by positivity
  have hmass :
      alpha * Fintype.card kappa * ((radius : Real) ^ 2 / 2) ≤
        Y.shadingMass.toReal :=
    densityLower_mul_card_half_sq_le_shadingMass_toReal
      hradiusHalf fine Y alpha halphaPos.le hdensity
  exact
    projectedShadedUnion_halfMass_le_explicitSharedHundredHull_originalUnion
      hsiteCount spacing fine shared Y f hf alpha
      ((radius : Real) ^ 2 / 2) halphaPos hcapPos hmass hKT

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {spacing : Real} {siteCount gridConstant : Nat}

/-- Selected hierarchy collision-cell specialization.  Its random-motion
geometry already supplies positivity and the half-radius bound; the collision
certificate supplies Katz--Tao.  Thus only the genuine shading-density lower
bound remains on the mass side. -/
theorem selectedHierarchyCollisionCell_uniformDensity_projectedShadedUnion_halfMass_le_explicit_originalUnion
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
    (alpha : Real) (halphaPos : 0 < alpha)
    (hdensity : ENNReal.ofReal alpha ≤ Y.shadingDensity) :
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
              (selectedHierarchyCollisionCellFamily H G joint k p a r) Y) /
          (siteCount : ENNReal)) := by
  have hKT :=
    selectedHierarchyCollisionCell_fullTranslatedFamily_isKatzTao
      grid joint wz k p hp a r baseD rho hspacing hrho source hselected
        hcluster
  exact
    uniformDensity_projectedShadedUnion_halfMass_le_explicitSharedHundredHull_originalUnion
      (G.childRadius_le_half k) (G.childRadius_pos k)
      hsiteCount spacing
      (selectedHierarchyCollisionCellFamily H G joint k p a r)
      (selectedHierarchyCollisionCell_sharedHundredSourceContainer
        H G joint k p a r)
      Y f hf alpha halphaPos hdensity hKT

#print axioms card_mul_half_sq_le_tubeBodyFamily_familyVolume
#print axioms densityLower_mul_card_half_sq_le_shadingMass_toReal
#print axioms uniformDensity_projectedShadedUnion_halfMass_le_explicitSharedHundredHull_originalUnion
#print axioms selectedHierarchyCollisionCell_uniformDensity_projectedShadedUnion_halfMass_le_explicit_originalUnion

end
end FamilyStickyHierarchyWZ2TranslatedCollisionCellUniformDensityExplicitHullV1
