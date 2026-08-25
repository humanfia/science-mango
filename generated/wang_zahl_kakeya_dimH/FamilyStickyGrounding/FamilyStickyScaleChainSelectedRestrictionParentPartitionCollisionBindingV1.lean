import FamilyStickyGrounding.FamilyStickyHierarchySelectedSourceNestedRestrictionV1
import FamilyStickyGrounding.FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainSelectedRestrictionParentPartitionCollisionBindingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentNormalizerReverseProducerV1
open FamilyStickyScaleChainHierarchySiblingRigidityV1
open FamilyStickyScaleChainHierarchySiblingRigidityProducerV1
open FamilyStickyScaleChainSelectedNestedSiblingRigidityProducerV1
open FamilyStickyScaleChainCollisionCellSiblingRigidityProducerV1
open FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyRandomLocalExactCarrierDedupV1
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1
open FamilyStickyHierarchySelectedSourceNestedRestrictionV1

noncomputable section

/-!
# Actual selected-restriction / parent-partition collision binding

The selected-source hierarchy and the sibling-rigidity producer used two
definitionally equivalent recursive descriptions of selected ancestors.  We
first prove that equivalence and expose the literal parent map of the rebuilt
selected hierarchy.

A bare `CoherentStickyMultiscaleCover` is nevertheless independent of the
hierarchy: it contains arbitrary-radius cover indices and parent maps, but no
map from those indices to the selected hierarchy.  The data-bearing seam below
therefore records coordinate maps into the *actual rebuilt selected hierarchy*
and their one commuting equation.  From those raw functions we construct the
injective lower realization, parent equivalence, and complete parent square;
none of those three certificates is accepted as an input.

For collision cells, substantially more is automatic.  Parent surjectivity
selects a real child of each active level-zero parent; the joint output's
positive repetition count selects repetition zero; and that occurrence gives
a literal `ModelCandidate`.  The only missing random-geometric statement is
that every other child of the same parent lies in that canonical candidate's
`100 T` collision cell.  A single proposition records precisely this uniform
coverage.  It automatically generates the old per-parent capture and hence the
concrete `parentCount * commonHundredNeighbourPackingConstant` reverse and
Sticky endpoints.
-/

universe u

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)

/-! ## The two selected ancestor recursions are the same -/

/-- The sibling producer's recursion is exactly the selected hierarchy's
parent-image recursion at every level. -/
theorem nestedLevelIndices_eq_selectedLevelIndices
    (selected : Finset (Index 0)) (l : Nat) :
    nestedLevelIndices H selected l =
      selectedLevelIndices H selected l := by
  induction l with
  | zero => rfl
  | succ l ih =>
      by_cases hl : l < depth
      · rw [nestedLevelIndices_succ H selected l hl,
          selectedLevelIndices_succ selected l hl]
        simpa [RestrictedStep.restrictedParents] using
          congrArg (fun A => A.image (H.step l hl).parentIndex) ih
      · simp [nestedLevelIndices, selectedLevelIndices, hl]

variable
  (R : SelectedTerminalSourceChartBucketGeometry (H := H))

/-- Forget only which recursion supplied the selected-level membership proof. -/
def selectedHierarchyIndexToNestedIndex (l : Nat) :
    SelectedHierarchyIndex R l ↪ SelectedLevelIndex H R.selected l where
  toFun := fun i => ⟨i.1, by
    rw [nestedLevelIndices_eq_selectedLevelIndices H R.selected l]
    exact i.2⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg
      (fun z : SelectedLevelIndex H R.selected l => z.1) hij

/-! ## The exact cover-to-selected-hierarchy seam -/

/--
Raw coordinates identifying arbitrary-radius cover parents with the concrete
selected hierarchy.  These are functions plus injectivity and the literal
restricted-step equation; no `Embedding`, `parent_eq_iff`, or
`ParentSquareIdentification` is stored.

The repository currently has no producer of these coordinates from a bare
`CoherentStickyMultiscaleCover`; the finite obstruction below shows why the
selected hierarchy alone cannot manufacture them.
-/
structure SelectedRestrictionCoverCoordinates where
  lowerCoordinate : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    LowerActiveParent H C S m rho hTauRho hRhoTheta ->
      SelectedHierarchyIndex R m.1
  lowerCoordinate_injective : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    Function.Injective (lowerCoordinate m rho hTauRho hRhoTheta)
  upperCoordinate : forall (m : Fin depth) (rho : NNReal)
      (_hTauRho : S.tau m <= rho) (_hRhoTheta : rho <= S.theta m),
    UpperActiveParent H C S m -> SelectedHierarchyIndex R (m.1 + 1)
  upperCoordinate_injective : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    Function.Injective (upperCoordinate m rho hTauRho hRhoTheta)
  restricted_parent_commutes : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (q : LowerActiveParent H C S m rho hTauRho hRhoTheta),
    (H.step m.1 m.2).parentIndex
        (lowerCoordinate m rho hTauRho hRhoTheta q).1 =
      (upperCoordinate m rho hTauRho hRhoTheta
        (crossParentOfLower H C S m rho hTauRho hRhoTheta q)).1

namespace SelectedRestrictionCoverCoordinates

variable {H C S R}
  (X : SelectedRestrictionCoverCoordinates H C S R)

/-- The raw lower coordinate becomes the selected-nested embedding
automatically, using the proved equality of the two recursions. -/
def lowerNestedEmbedding
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    LowerActiveParent H C S m rho hTauRho hRhoTheta ↪
      SelectedLevelIndex H R.selected m.1 where
  toFun := fun q => selectedHierarchyIndexToNestedIndex H R m.1
    (X.lowerCoordinate m rho hTauRho hRhoTheta q)
  inj' := (selectedHierarchyIndexToNestedIndex H R m.1).injective.comp
    (X.lowerCoordinate_injective m rho hTauRho hRhoTheta)
@[simp] theorem lowerNestedEmbedding_val
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (q : LowerActiveParent H C S m rho hTauRho hRhoTheta) :
    (X.lowerNestedEmbedding m rho hTauRho hRhoTheta q).1 =
      (X.lowerCoordinate m rho hTauRho hRhoTheta q).1 :=
  rfl


/-- Commutation in the concrete restricted hierarchy automatically gives
the parent-equivalence field required by selected sibling rigidity. -/
theorem crossParent_eq_iff_originalParent_eq
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (q q' : LowerActiveParent H C S m rho hTauRho hRhoTheta) :
    crossParentOfLower H C S m rho hTauRho hRhoTheta q =
        crossParentOfLower H C S m rho hTauRho hRhoTheta q' ↔
      (H.step m.1 m.2).parentIndex
          ((X.lowerNestedEmbedding m rho hTauRho hRhoTheta q).1) =
        (H.step m.1 m.2).parentIndex
          ((X.lowerNestedEmbedding m rho hTauRho hRhoTheta q').1) := by
  constructor
  · intro hcross
    have hu := congrArg
      (fun p : UpperActiveParent H C S m =>
        (X.upperCoordinate m rho hTauRho hRhoTheta p).1) hcross
    simpa only [lowerNestedEmbedding_val] using
      (X.restricted_parent_commutes m rho hTauRho hRhoTheta q).trans
        (hu.trans
          (X.restricted_parent_commutes m rho hTauRho hRhoTheta q').symm)
  · intro hp
    apply X.upperCoordinate_injective m rho hTauRho hRhoTheta
    apply Subtype.ext
    have hraw :
        (H.step m.1 m.2).parentIndex
            (X.lowerCoordinate m rho hTauRho hRhoTheta q).1 =
          (H.step m.1 m.2).parentIndex
            (X.lowerCoordinate m rho hTauRho hRhoTheta q').1 := by
      simpa only [lowerNestedEmbedding_val] using hp
    exact
      (X.restricted_parent_commutes m rho hTauRho hRhoTheta q).symm.trans
        (hraw.trans
          (X.restricted_parent_commutes m rho hTauRho hRhoTheta q'))

/-- The concrete selected-source geometry supplies level-zero activity; the
raw coordinate functions now automatically produce the old realization. -/
def toSelectedNestedParentRealization :
    SelectedNestedParentRealization H C S R.selected where
  selected_subset_refined := by
    simpa only [levelZeroSource] using R.selected_subset_source
  lowerEmbedding := X.lowerNestedEmbedding
  parent_eq_iff := X.crossParent_eq_iff_originalParent_eq

/-- Consequently the full lower/upper embeddings and parent square are
generated rather than supplied. -/
def toParentSquareIdentification : ParentSquareIdentification H C S :=
  (X.toSelectedNestedParentRealization).toParentSquareIdentification

end SelectedRestrictionCoverCoordinates

/-! ## Canonical cells supplied as far as the joint output permits -/

variable
  (G : HierarchyRandomMotionGeometry H)
  (J : HierarchyJointRandomMotionCertificate H G)

variable {H C S R G J}

/-- Every active level-zero hierarchy parent has a literal child in its
certified hierarchy fibre. -/
theorem levelZeroParentFiber_nonempty
    {hdepth : 0 < depth} (p : LevelZeroActiveParent H hdepth) :
    ((H.step 0 hdepth).combinatorics.index.fiber p.1).Nonempty := by
  obtain ⟨i, hi, hip⟩ :=
    (H.step 0 hdepth).combinatorics.parent_surjective p.1 p.2
  exact ⟨i, ((H.step 0 hdepth).combinatorics.index.mem_fiber i p.1).2
    ⟨hi, hip⟩⟩

/-- Canonical real child chosen from the actual parent fibre. -/
def canonicalLevelZeroParentChild
    {hdepth : 0 < depth} (p : LevelZeroActiveParent H hdepth) :
    {i // i ∈ (H.step 0 hdepth).combinatorics.index.fiber p.1} :=
  ⟨Classical.choose (levelZeroParentFiber_nonempty (H := H) p),
    Classical.choose_spec (levelZeroParentFiber_nonempty (H := H) p)⟩

/-- The joint output proves repetition zero is a valid actual repetition. -/
def canonicalLevelZeroRepetition
    {hdepth : 0 < depth} :
    Fin (repetitions G.toDependentSource (zeroLayer hdepth)) :=
  ⟨0, J.repetitions_one_le (zeroLayer hdepth)⟩

/-- Membership in a hierarchy parent fibre is definitionally membership in
that parent's actual collision grid source. -/
theorem levelZeroParentChild_mem_collisionGrid
    {hdepth : 0 < depth} (p : LevelZeroActiveParent H hdepth)
    (i : Index 0)
    (hi : i ∈ (H.step 0 hdepth).combinatorics.index.fiber p.1) :
    i ∈ (hierarchyCollisionGrid H G J (zeroLayer hdepth) p.1).tubes := by
  change i ∈ (H.step 0 hdepth).combinatorics.index.fiber p.1
  exact hi

/-- The actual fibre child at repetition zero determines a concrete model
candidate; candidate choice is not an additional field. -/
def canonicalLevelZeroParentCandidate
    {hdepth : 0 < depth} (p : LevelZeroActiveParent H hdepth) :
    ModelCandidate
      (hierarchyCollisionGrid H G J (zeroLayer hdepth) p.1) :=
  (⟨(canonicalLevelZeroParentChild (H := H) p).1,
      levelZeroParentChild_mem_collisionGrid (H := H) (G := G) (J := J) p
        (canonicalLevelZeroParentChild (H := H) p).1
        (canonicalLevelZeroParentChild (H := H) p).2⟩,
    (J.output.layerOutput (zeroLayer hdepth)).omega
      (canonicalLevelZeroRepetition (G := G) (J := J)))

/-- The canonical base child is automatically in its own real collision
cell.  Thus the missing field below is genuinely only uniform coverage of
the *other* children. -/
theorem canonicalLevelZeroParentChild_mem_candidateCell
    {hdepth : 0 < depth} (p : LevelZeroActiveParent H hdepth) :
    (canonicalLevelZeroParentChild (H := H) p).1 ∈
      candidateCollisionFinset
        (hierarchyCollisionGrid H G J (zeroLayer hdepth) p.1)
        (canonicalLevelZeroParentCandidate (H := H) (G := G) (J := J) p)
        ((J.output.layerOutput (zeroLayer hdepth)).omega
          (canonicalLevelZeroRepetition (G := G) (J := J))) := by
  apply (mem_candidateCollisionFinset _ _ _ _).2
  refine ⟨levelZeroParentChild_mem_collisionGrid
    (H := H) (G := G) (J := J) p _
      (canonicalLevelZeroParentChild (H := H) p).2, ?_⟩
  simpa [canonicalLevelZeroParentCandidate, modelCandidateTube] using
    carrier_subset_hundredTube
      (modelCandidateTube
        (hierarchyCollisionGrid H G J (zeroLayer hdepth) p.1)
        (canonicalLevelZeroParentCandidate (H := H) (G := G) (J := J) p))

/--
The sole per-parent random-geometric field not present in the current output:
the canonical cell through the canonical fibre child also covers every other
child of that same parent.  Candidate and repetition are definitions above,
not fields of this proposition.
-/
def CanonicalLevelZeroParentCellCoverage (hdepth : 0 < depth) : Prop :=
  forall (p : LevelZeroActiveParent H hdepth) (i : Index 0),
    i ∈ (H.step 0 hdepth).combinatorics.index.fiber p.1 ->
      i ∈ candidateCollisionFinset
        (hierarchyCollisionGrid H G J (zeroLayer hdepth) p.1)
        (canonicalLevelZeroParentCandidate (H := H) (G := G) (J := J) p)
        ((J.output.layerOutput (zeroLayer hdepth)).omega
          (canonicalLevelZeroRepetition (G := G) (J := J)))

/-- The minimal coverage statement automatically builds the complete old
parent-partition capture. -/
def parentPartitionCaptureOfCanonicalCoverage
    {hdepth : 0 < depth}
    (U : CanonicalLevelZeroParentCellCoverage (H := H) (G := G) (J := J)
      hdepth) :
    LevelZeroParentPartitionCollisionCellCapture H G J hdepth where
  parentCell := fun p => {
    candidate := canonicalLevelZeroParentCandidate (H := H) (G := G) (J := J) p
    repetition := canonicalLevelZeroRepetition (G := G) (J := J)
    contains_fiber := U p }

/-! ## Concrete parent-count-times-WZ endpoints -/

variable
  (X : SelectedRestrictionCoverCoordinates H C S R)

include X

/-- Actual reverse-normalizer endpoint after all structural and random raw
data have been converted to the existing audited producers. -/
theorem actualReverseParentNormalizerLoss_le_parentCount_mul_WZ
    {hdepth : 0 < depth}
    (U : CanonicalLevelZeroParentCellCoverage (H := H) (G := G) (J := J)
      hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    (hcompat : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : Index 0),
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    actualReverseParentNormalizerLoss C S <=
      hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
        (16 *
          ((levelZeroParentCount H hdepth *
            commonHundredNeighbourPackingConstant : Nat) : ENNReal)) := by
  exact
    actualReverseParentNormalizerLoss_le_of_parentPartitionCollisionCells
      W hdelta hhalf
        (SelectedRestrictionCoverCoordinates.toSelectedNestedParentRealization X)
        (parentPartitionCaptureOfCanonicalCoverage U) hcompat

/-- Arbitrary-radius Sticky endpoint with the literal
`parentCount * commonHundredNeighbourPackingConstant` occurrence loss. -/
theorem isStickyAtEveryScale_parentCount_mul_WZ
    {epsilon : Real}
    (hdepth : 0 < depth) (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    (W : HierarchyLevelWZSeparationData H)
    (U : CanonicalLevelZeroParentCellCoverage (H := H) (G := G) (J := J)
      hdepth) :
    C.base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
          (16 *
            ((levelZeroParentCount H hdepth *
              commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
        frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_parentPartitionCollisionCells
    hdepth hdelta hhalf D B W
      (SelectedRestrictionCoverCoordinates.toSelectedNestedParentRealization X)
      (parentPartitionCaptureOfCanonicalCoverage U)

/-! ## Sharp finite obstructions -/

/-- Selected parent-image recursion cannot create a lower-coordinate
injection when an independent cover has two active parents but the selected
hierarchy level has one occurrence. -/
theorem no_twoCoverParents_into_oneSelectedOccurrence :
    Not (Nonempty (Fin 2 ↪ Fin 1)) := by
  intro h
  obtain ⟨E⟩ := h
  have hcard := Fintype.card_le_of_embedding E
  norm_num at hcard

/-- Pointwise availability of a collision cell for every child does not give
one cell covering the whole fibre.  In this two-child/two-cell model each
child lies only in its own cell. -/
theorem pointwiseCells_do_not_produce_uniformParentCell :
    (forall i : Fin 2, exists a : Fin 2, i = a) ∧
      Not (exists a : Fin 2, forall i : Fin 2, i = a) := by
  constructor
  · intro i
    exact ⟨i, rfl⟩
  · rintro ⟨a, ha⟩
    have h0 := ha 0
    have h1 := ha 1
    have : (0 : Fin 2) = 1 := h0.trans h1.symm
    norm_num at this

#print axioms nestedLevelIndices_eq_selectedLevelIndices
#print axioms selectedHierarchyIndexToNestedIndex
#print axioms SelectedRestrictionCoverCoordinates.lowerNestedEmbedding
#print axioms SelectedRestrictionCoverCoordinates.crossParent_eq_iff_originalParent_eq
#print axioms SelectedRestrictionCoverCoordinates.toSelectedNestedParentRealization
#print axioms SelectedRestrictionCoverCoordinates.toParentSquareIdentification
#print axioms levelZeroParentFiber_nonempty
#print axioms canonicalLevelZeroParentChild
#print axioms canonicalLevelZeroRepetition
#print axioms levelZeroParentChild_mem_collisionGrid
#print axioms canonicalLevelZeroParentCandidate
#print axioms canonicalLevelZeroParentChild_mem_candidateCell
#print axioms parentPartitionCaptureOfCanonicalCoverage
#print axioms actualReverseParentNormalizerLoss_le_parentCount_mul_WZ
#print axioms isStickyAtEveryScale_parentCount_mul_WZ
#print axioms no_twoCoverParents_into_oneSelectedOccurrence
#print axioms pointwiseCells_do_not_produce_uniformParentCell

end
end FamilyStickyScaleChainSelectedRestrictionParentPartitionCollisionBindingV1
