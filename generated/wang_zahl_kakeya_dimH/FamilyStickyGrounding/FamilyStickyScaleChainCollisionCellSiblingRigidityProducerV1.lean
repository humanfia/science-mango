import FamilyStickyGrounding.FamilyStickyScaleChainSelectedNestedSiblingRigidityProducerV1
import FamilyStickyGrounding.FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainCollisionCellSiblingRigidityProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAtEveryScaleCoreV1.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentNormalizerReverseProducerV1
open FamilyStickyScaleChainHierarchySiblingRigidityV1
open FamilyStickyScaleChainHierarchySiblingRigidityProducerV1
open FamilyStickyScaleChainSelectedNestedSiblingRigidityProducerV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1

noncomputable section

/-!
# A collision-cell source for dimension-only sibling rigidity

The automatic selected-nested producer bounds an arbitrary lower occurrence
fiber by the ambient cardinality `Fintype.card (Index 0)`.  The existing WZ
packing theorem does not bound that ambient type: it bounds the literal
subtype in one `candidateCollisionFinset` of one hierarchy parent, model
candidate, and chosen repetition.

This file isolates the exact geometric bridge which would make that local
bound applicable.  A `LevelZeroCollisionCellCapture` records that every
active level-zero source index belongs to one concrete collision cell of the
actual hierarchy random-motion output.  The record stores membership, not a
cardinality inequality.  It therefore constructs an embedding into the real
collision-cell subtype, after which the repository's WZ separation and
common-`100 T` container theorem supply the dimension-only bound.

The resulting occurrence code has loss
`commonHundredNeighbourPackingConstant`, so tube-volume uniformity gives the
sibling-mass loss `16 * commonHundredNeighbourPackingConstant` and closes the
actual reverse normalizer and arbitrary-radius Sticky endpoint.

This bridge is conditional because the current hierarchy output supplies
only parent-local collision cells.  The closing theorem gives the sharp
structural obstruction: if two active initial sources have different honest
level-zero parents, no single-cell capture can exist.  In particular the
independent FixedGrid `siteCount` certificate cannot provide this missing
source-to-cell membership map.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)

/-- The literal first layer of a nonempty hierarchy. -/
def zeroLayer (hdepth : 0 < depth) : Fin depth :=
  ⟨0, hdepth⟩

variable (G : HierarchyRandomMotionGeometry H)
  (J : HierarchyJointRandomMotionCertificate H G)

/--
The minimal real source-to-cell bridge.  All fields name data already present
in the hierarchy collision grid; the sole missing fact is literal membership
of every active initial source in that one selected cell.
-/
structure LevelZeroCollisionCellCapture (hdepth : 0 < depth) where
  parent : Index 1
  parent_mem : parent ∈
    (G.toDependentSource.layer (zeroLayer hdepth)).activeParents
  candidate : ModelCandidate
    (hierarchyCollisionGrid H G J (zeroLayer hdepth) parent)
  repetition : Fin (repetitions G.toDependentSource (zeroLayer hdepth))
  contains_active : forall i : Index 0,
    i ∈ (H.effectiveFamily 0).refinement.refined ->
      i ∈ candidateCollisionFinset
        (hierarchyCollisionGrid H G J (zeroLayer hdepth) parent)
        candidate
        ((J.output.layerOutput (zeroLayer hdepth)).omega repetition)

namespace LevelZeroCollisionCellCapture

variable {H C S G J} {hdepth : 0 < depth}
  (Z : LevelZeroCollisionCellCapture H G J hdepth)

/-- The exact hierarchy collision-cell subtype selected by the capture. -/
abbrev CellIndex :=
  SelectedHierarchyCollisionCellIndex H G J (zeroLayer hdepth)
    Z.parent Z.candidate Z.repetition

/-- Active initial sources embed by their unchanged hierarchy index into the
literal selected collision-cell subtype. -/
def activeSourceEmbedding :
    {i // i ∈ (H.effectiveFamily 0).refinement.refined} ↪ Z.CellIndex where
  toFun := fun i => ⟨i.1, Z.contains_active i.1 i.2⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x : Z.CellIndex => x.1) hij

/-- Every actual lower cover fiber is a subtype of the active initial source,
and hence embeds into the selected hierarchy collision cell. -/
def lowerFiberEmbedding
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (q : LowerActiveParent H C S m rho hTauRho hRhoTheta) :
    {i // i ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).fiber q.1} ↪
      Z.CellIndex where
  toFun := fun i => ⟨i.1, Z.contains_active i.1 (by
    let L := lowerScaleCover C S m rho hTauRho hRhoTheta
    have hiActive : i.1 ∈ L.activeFine :=
      ((L.mem_fiber i.1 q.1).1 i.2).1
    rw [L.activeFine_eq_refined] at hiActive
    exact hiActive)⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x : Z.CellIndex => x.1) hij

/-- The existing common-`100 T` WZ theorem bounds the captured cell.  No
cardinality bound is stored in `Z`. -/
theorem cell_card_le_commonHundredNeighbourPackingConstant
    (W : HierarchyLevelWZSeparationData H) :
    Fintype.card Z.CellIndex <= commonHundredNeighbourPackingConstant := by
  exact
    selectedHierarchyCollisionCell_card_le_commonHundredNeighbourPackingConstant
      H G J W (zeroLayer hdepth) Z.parent Z.parent_mem
        Z.candidate Z.repetition

/-- Composition through the actual collision-cell subtype replaces the
ambient `card (Index 0)` occurrence loss by the dimension-only WZ packing
constant. -/
def siblingOccurrenceCode
    (W : HierarchyLevelWZSeparationData H) :
    SiblingOccurrenceCode H C S commonHundredNeighbourPackingConstant where
  fiberEmbedding := by
    intro m rho hTauRho hRhoTheta k hk q
    let L := lowerScaleCover C S m rho hTauRho hRhoTheta
    have hsourceCell :
        Fintype.card {i // i ∈ L.fiber q.1} <=
          Fintype.card Z.CellIndex :=
      Fintype.card_le_of_embedding
        (Z.lowerFiberEmbedding m rho hTauRho hRhoTheta
          (lowerActiveOfSibling H C S m rho hTauRho hRhoTheta k q))
    have hsource :
        Fintype.card {i // i ∈ L.fiber q.1} <=
          commonHundredNeighbourPackingConstant :=
      hsourceCell.trans
        (Z.cell_card_le_commonHundredNeighbourPackingConstant W)
    have hnonempty : (L.fiber k).Nonempty :=
      activeCoarse_fiber_nonempty L k hk
    have hpos : 0 < (L.fiber k).card := Finset.card_pos.mpr hnonempty
    have hcard :
        Fintype.card {i // i ∈ L.fiber q.1} <=
          Fintype.card
            (Fin commonHundredNeighbourPackingConstant ×
              {i // i ∈ L.fiber k}) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
        hsource.trans
          (Nat.le_mul_of_pos_right commonHundredNeighbourPackingConstant hpos)
    exact (Function.Embedding.nonempty_of_card_le hcard).some

end LevelZeroCollisionCellCapture

/-! ## Dimension-only reverse-normalizer production -/

variable {H C S G J}

/-- Selected nesting produces the parent square, while the actual captured
collision cell produces the dimension-only sibling occurrence code. -/
def collisionCellSelectedNestedSiblingRigidityCertificate
    {hdepth : 0 < depth}
    (W : HierarchyLevelWZSeparationData H)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected)
    (Z : LevelZeroCollisionCellCapture H G J hdepth) :
    HierarchySiblingRigidityCertificate H C S
      (hierarchyBranchingBound H)
      (16 * (commonHundredNeighbourPackingConstant : ENNReal)) :=
  hierarchySiblingRigidityCertificate hhalf
    R.toParentSquareIdentification (Z.siblingOccurrenceCode W)

/-- The actual reverse-parent loss now has a dimension-only occurrence
factor, rather than `Fintype.card (Index 0)`. -/
theorem actualReverseParentNormalizerLoss_le_of_collisionCellCapture
    {hdepth : 0 < depth}
    (W : HierarchyLevelWZSeparationData H)
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected)
    (Z : LevelZeroCollisionCellCapture H G J hdepth)
    (hcompat : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : Index 0),
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    actualReverseParentNormalizerLoss C S <=
      hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
        (16 * (commonHundredNeighbourPackingConstant : ENNReal)) := by
  exact actualReverseParentNormalizerLoss_le_of_parentSquare_occurrenceCode
    hdelta hhalf R.toParentSquareIdentification
      (Z.siblingOccurrenceCode W) hcompat

/-- End-to-end arbitrary-radius Sticky with the dimension-only WZ
neighbour-packing factor. -/
theorem isStickyAtEveryScale_of_collisionCellCapture
    {epsilon : Real}
    (hdepth : 0 < depth) (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    (W : HierarchyLevelWZSeparationData H)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected)
    (Z : LevelZeroCollisionCellCapture H G J hdepth) :
    C.base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
          (16 * (commonHundredNeighbourPackingConstant : ENNReal)) *
        frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_parentSquare_occurrenceCode
    hdepth hdelta hhalf D B R.toParentSquareIdentification
      (Z.siblingOccurrenceCode W)

/-! ## The exact missing source-to-cell field -/

variable {hdepth : 0 < depth}

/-- Membership in a level-zero hierarchy collision cell forces membership in
the one parent-local grid, hence fixes the honest hierarchy parent. -/
theorem levelZero_cell_member_parent_eq
    (p : Index 1)
    (a : ModelCandidate
      (hierarchyCollisionGrid H G J (zeroLayer hdepth) p))
    (r : Fin (repetitions G.toDependentSource (zeroLayer hdepth)))
    (i : Index 0)
    (hi : i ∈ candidateCollisionFinset
      (hierarchyCollisionGrid H G J (zeroLayer hdepth) p) a
      ((J.output.layerOutput (zeroLayer hdepth)).omega r)) :
    (H.step 0 hdepth).parentIndex i = p := by
  have hiGrid :=
    ((mem_candidateCollisionFinset
      (hierarchyCollisionGrid H G J (zeroLayer hdepth) p) a
      ((J.output.layerOutput (zeroLayer hdepth)).omega r) i).mp hi).1
  change i ∈ (H.step 0 hdepth).combinatorics.index.fiber p at hiGrid
  exact ((H.step 0 hdepth).combinatorics.index.mem_fiber i p).mp hiGrid |>.2

/-- Every active source captured by `Z` therefore has the same honest
level-zero parent. -/
theorem LevelZeroCollisionCellCapture.active_parent_eq
    (Z : LevelZeroCollisionCellCapture H G J hdepth)
    (i : Index 0) (hi : i ∈ (H.effectiveFamily 0).refinement.refined) :
    (H.step 0 hdepth).parentIndex i = Z.parent :=
  levelZero_cell_member_parent_eq (H := H) (G := G) (J := J) (hdepth := hdepth) Z.parent Z.candidate Z.repetition i
    (Z.contains_active i hi)

/-- Sharp obstruction supplied by the real parent-local grid: two active
initial sources with distinct honest parents cannot both be captured by one
collision cell.  This is precisely the map/equality missing from the current
selected hierarchy and FixedGrid APIs. -/
theorem no_levelZeroCollisionCellCapture_of_distinct_active_parents
    (i j : Index 0)
    (hi : i ∈ (H.effectiveFamily 0).refinement.refined)
    (hj : j ∈ (H.effectiveFamily 0).refinement.refined)
    (hparent : (H.step 0 hdepth).parentIndex i ≠
      (H.step 0 hdepth).parentIndex j) :
    Not (Nonempty (LevelZeroCollisionCellCapture H G J hdepth)) := by
  rintro ⟨Z⟩
  apply hparent
  exact (Z.active_parent_eq i hi).trans (Z.active_parent_eq j hj).symm

#print axioms zeroLayer
#print axioms LevelZeroCollisionCellCapture.activeSourceEmbedding
#print axioms LevelZeroCollisionCellCapture.lowerFiberEmbedding
#print axioms LevelZeroCollisionCellCapture.cell_card_le_commonHundredNeighbourPackingConstant
#print axioms LevelZeroCollisionCellCapture.siblingOccurrenceCode
#print axioms collisionCellSelectedNestedSiblingRigidityCertificate
#print axioms actualReverseParentNormalizerLoss_le_of_collisionCellCapture
#print axioms isStickyAtEveryScale_of_collisionCellCapture
#print axioms levelZero_cell_member_parent_eq
#print axioms LevelZeroCollisionCellCapture.active_parent_eq
#print axioms no_levelZeroCollisionCellCapture_of_distinct_active_parents

end
end FamilyStickyScaleChainCollisionCellSiblingRigidityProducerV1
