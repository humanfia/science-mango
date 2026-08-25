import FamilyStickyGrounding.FamilyStickyWZ2SharedHundredSourceConstantEndpointV1
import FamilyStickyGrounding.FamilyStickyHierarchyJointRandomMotionCertificateV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyWZ2TranslatedCopyDensityKatzTaoV1
open FamilyStickyWZ2ShearParameterPackingV1
open FamilyStickyWZ2AmbientShearContainedMassV1
open FamilyStickyWZ2JohnBoxVolumeNormalizationV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
open FamilyStickyWZ2DistortedJohnRadiusNormalizationV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyWZ2SharedHundredSourceConstantEndpointV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Hierarchy collision cells as fixed-constant WZ2 sources

Levelwise WZ separation automatically restricts to every parent fibre.  A
parent fibre is contained in its coarser parent tube, but that tube has the
next effective radius.  It is therefore a literal hundred-fold container at
the child radius only under the explicit adjacent-radius upper comparison
recorded below; the hierarchy currently supplies only the reverse inequality.

The collision event provides the unconditional local source actually used in
the random-motion proof.  For one parent, one model candidate, and one chosen
translation, `candidateCollisionFinset` consists exactly of all translated
children lying in the candidate's literal hundred-fold tube.  Translating the
single container back puts all original child tubes in one literal common
container.  The parent-fibre WZ separation restricts to this cell, so the
fixed source-factor WZ2 endpoint applies with no cardinality premise.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {spacing : Real} {siteCount : Nat}

/-- The exact scalar condition under which an entire hierarchy parent fibre
fits into the hundred-fold dilation of an equal-child-radius parent axis. -/
def HierarchyParentHundredRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Prop :=
  forall k : Fin depth,
    H.effectiveRadius (k.1 + 1) <= hundredRadius (H.effectiveRadius k.1)

/-- The literal child family in one hierarchy parent fibre. -/
def hierarchyParentFibreFamily
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1)) :
    UniformTubeFamily (H.effectiveRadius k.1)
      {i // i ∈ (H.step k.1 k.2).combinatorics.index.fiber p} :=
  (H.effectiveFamily k.1).restrictTo
    ((H.step k.1 k.2).combinatorics.index.fiber p)

/-- Existing hierarchy WZ data restricts to the full subtype of any parent
fibre, independently of a random-motion output. -/
theorem hierarchyParentFibreFamily_pairwise_WZEndpointParameterSeparated
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (W : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1)) :
    Set.Pairwise
      (Set.univ : Set
        {i // i ∈ (H.step k.1 k.2).combinatorics.index.fiber p})
      fun i j => WZEndpointParameterSeparated
        ((hierarchyParentFibreFamily H k p).tubes i)
        ((hierarchyParentFibreFamily H k p).tubes j) := by
  intro i _hi j _hj hij
  change WZEndpointParameterSeparated
    ((H.effectiveFamily k.1).tubes i.1)
    ((H.effectiveFamily k.1).tubes j.1)
  apply W.separated k.1 (Nat.le_of_lt k.2)
  · have hiFine : i.1 ∈
        (H.step k.1 k.2).combinatorics.index.fine :=
      (((H.step k.1 k.2).combinatorics.index.mem_fiber i.1 p).1 i.2).1
    rw [(H.step k.1 k.2).combinatorics.fine_eq_refined] at hiFine
    exact hiFine
  · have hjFine : j.1 ∈
        (H.step k.1 k.2).combinatorics.index.fine :=
      (((H.step k.1 k.2).combinatorics.index.mem_fiber j.1 p).1 j.2).1
    rw [(H.step k.1 k.2).combinatorics.fine_eq_refined] at hjFine
    exact hjFine
  · intro hijValue
    apply hij
    exact Subtype.ext hijValue

/-- With the missing adjacent-radius upper comparison made explicit, the
whole parent fibre has one honest literal hundred-fold container. -/
def hierarchyParentFibre_sharedHundredSourceContainer
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hratio : H.effectiveRadius (k.1 + 1) <=
      hundredRadius (H.effectiveRadius k.1)) :
    SharedHundredSourceContainer (hierarchyParentFibreFamily H k p) where
  container := ((H.effectiveFamily (k.1 + 1)).tubes p).changeRadius
    (H.effectiveRadius k.1)
  carrier_subset := by
    intro i
    have hiData :=
      ((H.step k.1 k.2).combinatorics.index.mem_fiber i.1 p).1 i.2
    have hiRef : i.1 ∈ (H.family k.1).refinement.refined := by
      rw [← (H.step k.1 k.2).combinatorics.fine_eq_refined]
      exact hiData.1
    have hchild := H.effective_carrier_subset_parent k.1 k.2 i.1 hiRef
    have hpEq : (H.step k.1 k.2).parentIndex i.1 = p := by
      simpa [AdjacentTubeStep.parentIndex] using hiData.2
    have hchild' :
        ((H.effectiveFamily k.1).tubes i.1).carrier <=
          ((H.effectiveFamily (k.1 + 1)).tubes p).carrier := by
      simpa [hpEq] using hchild
    apply hchild'.trans
    have hparent :=
      ((H.effectiveFamily (k.1 + 1)).tubes p).carrier_subset_changeRadius
        hratio
    change ((H.effectiveFamily (k.1 + 1)).tubes p).carrier <=
      (((H.effectiveFamily (k.1 + 1)).tubes p).changeRadius
        (hundredRadius (H.effectiveRadius k.1))).carrier
    exact hparent

/-- Source indices in one literal collision cell. -/
abbrev CollisionCellIndex
    {delta : NNReal} {translation tubeIndex : Type*}
    [Fintype translation] [DecidableEq translation] [DecidableEq tubeIndex]
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) (g : translation) :=
  {i // i ∈ candidateCollisionFinset G a g}

/-- A collision cell as a uniform tube family.  The subtype carries a fresh
scale-empty refinement; no quantitative retention is asserted. -/
def collisionCellSourceFamily
    {delta : NNReal} {translation tubeIndex : Type*}
    [Fintype translation] [DecidableEq translation] [DecidableEq tubeIndex]
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) (g : translation) :
    UniformTubeFamily delta (CollisionCellIndex G a g) where
  tubes := fun i => G.tube i.1
  refinement := UniformRefinement.ofFinset Finset.univ

/-- Undoing a common translation transports containment in one hundred-fold
tube to containment in the translated-back hundred-fold tube. -/
theorem carrier_subset_translatedBack_hundredTube
    {delta : NNReal} {T W : Tube delta} {v : Space}
    (hcontain : (translateTube T v).carrier <= (hundredTube W).carrier) :
    T.carrier <= (hundredTube (translateTube W (-v))).carrier := by
  intro x hx
  rw [← translateTube_hundredTube, translateTube_carrier]
  refine ⟨v + x, hcontain ?_, ?_⟩
  · rw [translateTube_carrier]
    exact ⟨x, hx, rfl⟩
  · simp

/-- Every collision-cell source family has one literal common hundred-fold
container, produced solely from membership in the collision finset. -/
def collisionCellSourceFamily_sharedHundredSourceContainer
    {delta : NNReal} {translation tubeIndex : Type*}
    [Fintype translation] [DecidableEq translation] [DecidableEq tubeIndex]
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (a : ModelCandidate G) (g : translation) :
    SharedHundredSourceContainer (collisionCellSourceFamily G a g) where
  container := translateTube (modelCandidateTube G a) (-G.gridVector g)
  carrier_subset := by
    intro i
    exact carrier_subset_translatedBack_hundredTube
      ((mem_candidateCollisionFinset G a g i.1).mp i.2).2

/-- Pairwise WZ separation of a source grid restricts to every one of its
literal collision cells. -/
theorem collisionCellSourceFamily_pairwise_WZEndpointParameterSeparated
    {delta : NNReal} {translation tubeIndex : Type*}
    [Fintype translation] [DecidableEq translation] [DecidableEq tubeIndex]
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated (G.tube i) (G.tube j))
    (a : ModelCandidate G) (g : translation) :
    Set.Pairwise (Set.univ : Set (CollisionCellIndex G a g)) fun i j =>
      WZEndpointParameterSeparated
        ((collisionCellSourceFamily G a g).tubes i)
        ((collisionCellSourceFamily G a g).tubes j) := by
  intro i _hi j _hj hij
  change WZEndpointParameterSeparated (G.tube i.1) (G.tube j.1)
  apply hpair
  · exact ((mem_candidateCollisionFinset G a g i.1).mp i.2).1
  · exact ((mem_candidateCollisionFinset G a g j.1).mp j.2).1
  · intro hijValue
    apply hij
    exact Subtype.ext hijValue

variable
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (G : HierarchyRandomMotionGeometry H)

/-- The actual collision grid belonging to one parent of one layer in the
joint hierarchy output. -/
abbrev hierarchyCollisionGrid
    (C : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1)) :=
  parentPackingGrid (G.toDependentSource.layer k)
    (C.output.layerOutput k).certificate p

/-- Existing levelwise hierarchy data supplies full WZ separation on every
active parent's actual collision grid. -/
theorem hierarchyCollisionGrid_pairwise_WZEndpointParameterSeparated
    (C : HierarchyJointRandomMotionCertificate H G)
    (W : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents) :
    Set.Pairwise ((hierarchyCollisionGrid H G C k p).tubes : Set (Index k.1))
      fun i j => WZEndpointParameterSeparated
        ((hierarchyCollisionGrid H G C k p).tube i)
        ((hierarchyCollisionGrid H G C k p).tube j) := by
  have hparent := hierarchy_parentFibreWZSeparated H G W k
  intro i hi j hj hij
  change WZEndpointParameterSeparated
    ((H.effectiveFamily k.1).tubes i)
    ((H.effectiveFamily k.1).tubes j)
  exact hparent p hp hi hj hij

/-- One selected random-motion collision cell, with its source subtype kept
literal. -/
abbrev SelectedHierarchyCollisionCellIndex
    (C : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin (repetitions G.toDependentSource k)) :=
  CollisionCellIndex (hierarchyCollisionGrid H G C k p) a
    ((C.output.layerOutput k).omega r)

/-- Uniform source family of one selected hierarchy collision cell. -/
abbrev selectedHierarchyCollisionCellFamily
    (C : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin (repetitions G.toDependentSource k)) :=
  collisionCellSourceFamily (hierarchyCollisionGrid H G C k p) a
    ((C.output.layerOutput k).omega r)

/-- The selected hierarchy collision cell has a canonical literal common
hundred-fold container. -/
def selectedHierarchyCollisionCell_sharedHundredSourceContainer
    (C : HierarchyJointRandomMotionCertificate H G)
    (k : Fin depth) (p : Index (k.1 + 1))
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin (repetitions G.toDependentSource k)) :
    SharedHundredSourceContainer
      (selectedHierarchyCollisionCellFamily H G C k p a r) :=
  collisionCellSourceFamily_sharedHundredSourceContainer _ _ _

/-- The selected hierarchy collision cell inherits full WZ separation from
its active parent fibre. -/
theorem selectedHierarchyCollisionCell_pairwise_WZEndpointParameterSeparated
    (C : HierarchyJointRandomMotionCertificate H G)
    (W : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin (repetitions G.toDependentSource k)) :
    Set.Pairwise
      (Set.univ : Set (SelectedHierarchyCollisionCellIndex H G C k p a r))
      fun i j => WZEndpointParameterSeparated
        ((selectedHierarchyCollisionCellFamily H G C k p a r).tubes i)
        ((selectedHierarchyCollisionCellFamily H G C k p a r).tubes j) := by
  exact collisionCellSourceFamily_pairwise_WZEndpointParameterSeparated
    (hierarchyCollisionGrid H G C k p)
    (hierarchyCollisionGrid_pairwise_WZEndpointParameterSeparated
      H G C W k p hp)
    a ((C.output.layerOutput k).omega r)

/-- Hence every selected hierarchy collision cell has the fixed WZ source
cardinality bound before any WZ2 analytic hypotheses are introduced. -/
theorem selectedHierarchyCollisionCell_card_le_commonHundredNeighbourPackingConstant
    (C : HierarchyJointRandomMotionCertificate H G)
    (W : HierarchyLevelWZSeparationData H)
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : ModelCandidate (hierarchyCollisionGrid H G C k p))
    (r : Fin (repetitions G.toDependentSource k)) :
    Fintype.card (SelectedHierarchyCollisionCellIndex H G C k p a r) <=
      commonHundredNeighbourPackingConstant := by
  exact fintype_card_le_commonHundredNeighbourPackingConstant
    (selectedHierarchyCollisionCellFamily H G C k p a r)
    (G.childRadius_pos k)
    (selectedHierarchyCollisionCell_pairwise_WZEndpointParameterSeparated
      H G C W k p hp a r)
    (selectedHierarchyCollisionCell_sharedHundredSourceContainer
      H G C k p a r)

/-- Fixed-source-factor distorted-John endpoint on the actual local source
selected by one hierarchy collision event. -/
theorem exists_selectedHierarchyCollisionCell_distortedJohnCertificate_and_containedMass_le_WZConstant
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
            ((min siteCount
              (Nat.ceil
                ((2 *
                  (4 * johnRadiusVolumeCap K (H.effectiveRadius k.1)
                    (shearSiteD spacing q) + rho)) / spacing) + 1) *
                commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
            volume (K : Set Space) := by
  let hshared := selectedHierarchyCollisionCell_sharedHundredSourceContainer
    H G C k p a r
  have hpair :=
    selectedHierarchyCollisionCell_pairwise_WZEndpointParameterSeparated
      H G C W k p hp a r
  exact
    exists_distortedJohnCertificate_and_containedMass_le_WZConstant_of_fixedVerticalChart
      (selectedHierarchyCollisionCellFamily H G C k p a r) K
      (G.childRadius_pos k) (G.childRadius_le_half k)
      q i hcontained baseD rho hspacing hrho hpair hshared source hselected
      hcluster

#print axioms hierarchyParentFibreFamily_pairwise_WZEndpointParameterSeparated
#print axioms hierarchyParentFibre_sharedHundredSourceContainer
#print axioms carrier_subset_translatedBack_hundredTube
#print axioms collisionCellSourceFamily_sharedHundredSourceContainer
#print axioms collisionCellSourceFamily_pairwise_WZEndpointParameterSeparated
#print axioms hierarchyCollisionGrid_pairwise_WZEndpointParameterSeparated
#print axioms selectedHierarchyCollisionCell_sharedHundredSourceContainer
#print axioms selectedHierarchyCollisionCell_pairwise_WZEndpointParameterSeparated
#print axioms selectedHierarchyCollisionCell_card_le_commonHundredNeighbourPackingConstant
#print axioms exists_selectedHierarchyCollisionCell_distortedJohnCertificate_and_containedMass_le_WZConstant

end
end FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
