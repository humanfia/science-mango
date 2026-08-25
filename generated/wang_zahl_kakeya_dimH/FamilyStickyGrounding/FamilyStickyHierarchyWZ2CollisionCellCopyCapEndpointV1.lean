import FamilyStickyGrounding.FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
import FamilyStickyGrounding.FamilyStickyWZ2CopyGridCapEndpointV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZ2CollisionCellCopyCapEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2AmbientShearContainedMassV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
open FamilyStickyWZ2DistortedJohnRadiusNormalizationV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyWZ2CopyGridCapEndpointV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Hierarchy collision-cell WZ2 endpoint with a fixed copy-grid cap

The selected collision-cell adapter produces the common literal `100T`
container and full WZ separation internally.  The copy-grid cap removes the
remaining John-volume ceiling.  Their composition gives one directly usable
local endpoint whose coefficient is exactly
`16 * siteCount * commonHundredNeighbourPackingConstant`.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {spacing : Real} {siteCount : Nat}

/-- Fully composed local hierarchy-to-WZ2 endpoint.  Neither a source-card
bound nor a convex-test-dependent copy ceiling is supplied by the caller. -/
theorem exists_selectedHierarchyCollisionCell_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant
    (C : HierarchyJointRandomMotionCertificate H G)
    (W : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin (repetitions G.toDependentSource k))
    (K : ConvexBody Space) (q : Fin siteCount)
    (i : SelectedHierarchyCollisionCellIndex H G C k p a r)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily
            (selectedHierarchyCollisionCellFamily H G C k p a r).tubes)
          (q, i) : ConvexBody Space) : Set Space) <= (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (source : Finset
      (SelectedHierarchyCollisionCellIndex H G C k p a r))
    (hselected :
      (Finset.univ : Finset
        (SelectedHierarchyCollisionCellIndex H G C k p a r)) <=
      fixedVerticalChartIndices
        (selectedHierarchyCollisionCellFamily H G C k p a r) source)
    (hcluster : forall l,
      |tubeGraphD
          ((selectedHierarchyCollisionCellFamily H G C k p a r).tubes l) -
        baseD| <= rho) :
    ∃ side : Fin 3 -> NNReal,
      ∃ _cert : BoxDimensionsCertificate 288 side K,
        (forall l,
          2 * distortedTubeRadius (H.effectiveRadius k.1)
            (shearSiteD spacing q) <= side l) ∧
        (∃ l : Fin 3,
          distortedAxisLength (shearSiteD spacing q) <= 6 * side l) ∧
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily
                (selectedHierarchyCollisionCellFamily H G C k p a r).tubes)) K <=
          (16 *
            ((siteCount * commonHundredNeighbourPackingConstant : Nat) :
              ENNReal)) *
            volume (K : Set Space) := by
  let hshared := selectedHierarchyCollisionCell_sharedHundredSourceContainer
    H G C k p a r
  have hpair :=
    selectedHierarchyCollisionCell_pairwise_WZEndpointParameterSeparated
      H G C W k p hp a r
  exact
    exists_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant_of_fixedVerticalChart
      (selectedHierarchyCollisionCellFamily H G C k p a r) K
      (G.childRadius_pos k) (G.childRadius_le_half k)
      q i hcontained baseD rho hspacing hrho hpair hshared source hselected
      hcluster

#print axioms exists_selectedHierarchyCollisionCell_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant

end
end FamilyStickyHierarchyWZ2CollisionCellCopyCapEndpointV1
