import FamilyStickyGrounding.FamilyStickyHierarchySuppliedPackingJointRandomMotionV1
import FamilyStickyGrounding.FamilyStickyHierarchyTerminalSamePathWZEliminationV1
import FamilyStickyGrounding.FamilyStickyScaleChainParentNormalizerReverseProducerV1
import FamilyStickyGrounding.FamilyStickyHierarchyWZ2CollisionCellCopyCapEndpointV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyFinalMultiscaleAssemblyCertificateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentMassLocalizationProducerV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentNormalizerReverseProducerV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchySuppliedPackingJointRandomMotionV1
open FamilyStickyHierarchyTerminalSamePathWZEliminationV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyWZ2CollisionCellCopyCapEndpointV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2AmbientShearContainedMassV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
open FamilyStickyWZ2DistortedJohnRadiusNormalizationV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1

noncomputable section

/-!
# A data-bearing checkpoint for the final Sticky assembly

This certificate puts four already proved branches over one literal hierarchy:

* a random-motion output using a packing plan fixed before selection;
* the arbitrary-radius Sticky bounds for the hierarchy's level-zero effective
  family, with the reverse parent-normalizer loss computed from the cover;
* the terminal exact-carrier multiplicity bound with the same-path source loss
  replaced by the fixed WZ packing constant; and
* every selected collision-cell distorted-John/WZ2 estimate for the very same
  joint random-motion output.

The bundle deliberately contains the local scale-cover geometry and discrete
endpoint bounds rather than a final-conclusion callback.  It also makes no
claim that a scale-cover endpoint family is equal to a hierarchy prefix or a
collision-cell family: that identification is the remaining non-numerical
geometry needed by a later final assembly.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (G : HierarchyRandomMotionGeometry H)
  (P : HierarchyPackingPlan.Plan H)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)

/-- The strongest safe assembly presently obtainable without identifying the
scale-cover endpoint families with the hierarchy's selected prefix families.
All analytic and collision conclusions below are derived from these fields. -/
structure Certificate
    (epsilon : Real)
    (massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal) where
  hierarchy : SuppliedHierarchy.Certificate H G P
  levelWZ : HierarchyLevelWZSeparationData H
  localGeometry : LargeIntervalLocalGeometry C S epsilon
    massLoss bodyLoss katzTaoLoss
  discreteBounds : DiscreteAllLargeStickyBounds C S epsilon
    frostmanError katzTaoError
  depth_pos : 0 < depth
  initialRadius_pos : 0 < H.effectiveRadius 0

namespace Certificate

variable {H G P C S}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
  (A : Certificate H G P C S epsilon
    massLoss bodyLoss katzTaoLoss frostmanError katzTaoError)

abbrev Path := A.hierarchy.Path

include A in
/-- The same certificate gives the actual-loss arbitrary-radius Sticky
statement for the hierarchy's literal level-zero effective family. -/
theorem stickyAtEveryScale :
    C.base.IsStickyAtEveryScale
      (actualReverseParentNormalizerLoss C S * frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_actualReverseParentNormalizerLoss
    C S A.depth_pos A.initialRadius_pos A.localGeometry A.discreteBounds

/-- The supplied packing plan and the joint output remain definitionally
coherent when a finite pre-motion hull catalogue is used. -/
theorem prefixFiber_isKatzTao_of_preMotion_finite_tests
    (path : A.Path) (k : Fin depth) (p : Index (k.1 + 1))
    (B : ENNReal)
    (hfinite : forall q,
      IsKatzTaoAt B
        (FixedPackingPotentialFamily.selectedFamily
          (hierarchyFiberSeedData H k p) (P.certificate k)
          (JointCertificateAdapter.plannedOmega
            A.hierarchy.joint P A.hierarchy.usesPlan k))
        ((HierarchyPackingPlan.parentCanonicalTestFamily H P G k p).testBody q)) :
    IsKatzTao B
      (FamilyStickyConvexBodyTranslationConcentrationV1.translateFamily
        (FixedPackingPotentialFamily.selectedFamily
          (hierarchyFiberSeedData H k p) (P.certificate k)
          (JointCertificateAdapter.plannedOmega
            A.hierarchy.joint P A.hierarchy.usesPlan k))
        (A.hierarchy.joint.output.prefixVector path k)) := by
  exact A.hierarchy.prefixFiber_isKatzTao_of_preMotion_finite_tests
    path k p B hfinite

/-- Terminal occurrences of this exact supplied-plan output have the fixed WZ
same-path loss and only the explicitly computed widened cross-parent loss. -/
theorem finalIndex_card_le_WZMultiplicity_mul_terminalStrongRepresentatives :
    Fintype.card A.hierarchy.joint.FinalIndex <=
      terminalExactCarrierWZMultiplicityBound A.hierarchy.joint *
        (FamilyStickyHierarchyTerminalCarrierDedupV1.terminalStrongMultiplicity
            A.hierarchy.joint *
          (FamilyStickyHierarchyTerminalCarrierDedupV1.terminalStrongRepresentatives
            A.hierarchy.joint).card) := by
  exact FamilyStickyHierarchyTerminalSamePathWZEliminationV1.finalIndex_card_le_WZMultiplicity_mul_terminalStrongRepresentatives
    A.hierarchy.joint A.initialRadius_pos A.levelWZ

/-- Carrier-dependent terminal loads inherit the same WZ replacement on the
same joint output stored in this certificate. -/
theorem terminal_weighted_load_le_WZMultiplicity_mul_representative_load
    (w : Set Space -> Nat) :
    (∑ a : A.hierarchy.joint.FinalIndex,
        w (FamilyStickyHierarchyTerminalCarrierDedupV1.terminalCarrier
          A.hierarchy.joint a)) <=
      terminalExactCarrierWZMultiplicityBound A.hierarchy.joint *
        ∑ a ∈
            FamilyStickyHierarchyTerminalCarrierDedupV1.terminalRepresentatives
              A.hierarchy.joint,
          w (FamilyStickyHierarchyTerminalCarrierDedupV1.terminalCarrier
            A.hierarchy.joint a) := by
  exact FamilyStickyHierarchyTerminalSamePathWZEliminationV1.terminal_weighted_load_le_WZMultiplicity_mul_representative_load
    A.hierarchy.joint A.initialRadius_pos A.levelWZ w

/-- Every actual selected collision cell from the stored joint output feeds
the fixed-copy-grid WZ2 endpoint.  No source-cardinality or John-ceiling
callback is part of the assembly certificate. -/
theorem exists_collisionCell_distortedJohnCertificate_and_containedMass_le
    {spacing : Real} {siteCount : Nat}
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate
      (hierarchyCollisionGrid H G A.hierarchy.joint k p))
    (r : Fin (repetitions G.toDependentSource k))
    (K : ConvexBody Space) (q : Fin siteCount)
    (i : SelectedHierarchyCollisionCellIndex
      H G A.hierarchy.joint k p a r)
    (hcontained :
      ((indexedTranslatedBodyFamily
          (shearReducedShift spacing (siteCount := siteCount))
          (tubeBodyFamily
            (selectedHierarchyCollisionCellFamily
              H G A.hierarchy.joint k p a r).tubes)
          (q, i) : ConvexBody Space) : Set Space) <= (K : Set Space))
    (baseD rho : Real) (hspacing : 0 < spacing) (hrho : 0 <= rho)
    (source : Finset
      (SelectedHierarchyCollisionCellIndex
        H G A.hierarchy.joint k p a r))
    (hselected :
      (Finset.univ : Finset
        (SelectedHierarchyCollisionCellIndex
          H G A.hierarchy.joint k p a r)) <=
      fixedVerticalChartIndices
        (selectedHierarchyCollisionCellFamily
          H G A.hierarchy.joint k p a r) source)
    (hcluster : forall l,
      |tubeGraphD
          ((selectedHierarchyCollisionCellFamily
            H G A.hierarchy.joint k p a r).tubes l) - baseD| <= rho) :
    exists side : Fin 3 -> NNReal,
      exists _cert : BoxDimensionsCertificate 288 side K,
        (forall l,
          2 * distortedTubeRadius (H.effectiveRadius k.1)
            (shearSiteD spacing q) <= side l) ∧
        (exists l : Fin 3,
          distortedAxisLength (shearSiteD spacing q) <= 6 * side l) ∧
        containedMass
            (indexedTranslatedBodyFamily
              (shearReducedShift spacing (siteCount := siteCount))
              (tubeBodyFamily
                (selectedHierarchyCollisionCellFamily
                  H G A.hierarchy.joint k p a r).tubes)) K <=
          (16 *
            ((siteCount * commonHundredNeighbourPackingConstant : Nat) :
              ENNReal)) *
            volume (K : Set Space) := by
  exact FamilyStickyHierarchyWZ2CollisionCellCopyCapEndpointV1.exists_selectedHierarchyCollisionCell_distortedJohnCertificate_and_containedMass_le_siteCount_mul_WZConstant
    A.hierarchy.joint A.levelWZ k p hp a r K q i hcontained
      baseD rho hspacing hrho source hselected hcluster

end Certificate

/-! ## Constructors -/

/-- Construct the combined checkpoint directly from a preselected hierarchy
packing plan.  The same selected joint output is then used by all terminal and
collision-cell methods above. -/
theorem exists_certificate_of_supplied_plan
    {epsilon : Real}
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale H G)
    (hdepth : 0 < depth) (hdelta : 0 < H.effectiveRadius 0)
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError) :
    Nonempty (Certificate H G P C S epsilon
      massLoss bodyLoss katzTaoLoss frostmanError katzTaoError) := by
  obtain ⟨Q⟩ := SuppliedHierarchy.exists_certificate_with_plan
    H G P W hcollisionUnit
  exact ⟨{
    hierarchy := Q
    levelWZ := W
    localGeometry := D
    discreteBounds := B
    depth_pos := hdepth
    initialRadius_pos := hdelta }⟩

/-- Canonical pre-motion-hull specialization.  The geometry used by the
selector is built from the same packing plan that is stored in the result. -/
theorem exists_preMotion_certificate_of_supplied_plan
    {epsilon : Real}
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (M : HierarchyPackingPlan.MeanScaleData H P G)
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale H
      (HierarchyPackingPlan.toPreMotionGeometry H P G M))
    (hdepth : 0 < depth) (hdelta : 0 < H.effectiveRadius 0)
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError) :
    Nonempty (Certificate H
      (HierarchyPackingPlan.toPreMotionGeometry H P G M) P C S epsilon
      massLoss bodyLoss katzTaoLoss frostmanError katzTaoError) := by
  obtain ⟨Q⟩ := SuppliedHierarchy.exists_preMotion_certificate_with_plan
    H G P M W hcollisionUnit
  exact ⟨{
    hierarchy := Q
    levelWZ := W
    localGeometry := D
    discreteBounds := B
    depth_pos := hdepth
    initialRadius_pos := hdelta }⟩

#print axioms Certificate.stickyAtEveryScale
#print axioms Certificate.prefixFiber_isKatzTao_of_preMotion_finite_tests
#print axioms Certificate.finalIndex_card_le_WZMultiplicity_mul_terminalStrongRepresentatives
#print axioms Certificate.terminal_weighted_load_le_WZMultiplicity_mul_representative_load
#print axioms Certificate.exists_collisionCell_distortedJohnCertificate_and_containedMass_le
#print axioms exists_certificate_of_supplied_plan
#print axioms exists_preMotion_certificate_of_supplied_plan

end
end FamilyStickyFinalMultiscaleAssemblyCertificateV1
