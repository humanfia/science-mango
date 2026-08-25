import FamilyStickyGrounding.FamilyStickyScaleChainCollisionCellSiblingRigidityProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1

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
open FamilyStickyScaleChainCollisionCellSiblingRigidityProducerV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyWZ2CollisionCellSourceAdapterV1

noncomputable section

/-!
# Parent-partitioned collision cells for sibling rigidity

The single-cell producer asks every active level-zero source to lie in one
parent-local collision cell.  This file removes that condition.  The honest
level-zero hierarchy partition is retained: for each active parent `p`, one
actual candidate and one actual repetition capture only the literal fibre of
`p`.  The existing common-`100 T` WZ theorem caps every such cell, and the
hierarchy's exact fibre-sum identity then gives

`levelZeroParentCount * commonHundredNeighbourPackingConstant`.

This is fed into the occurrence-code and tube-volume producers, yielding the
corresponding `16`-fold sibling-mass loss, actual reverse-normalizer bound,
and arbitrary-radius Sticky endpoint.  No source is required to enter a cell
belonging to a different parent.

Existing hierarchy branching bounds children per parent, not the number of
parents.  The widened source bounds retain the same parent-count factor.
Accordingly an optional finite parent code is isolated as the minimal datum
which can replace the actual parent count by a fixed one.  The final
singleton-parent model is sharp: arbitrarily many parents may each have a
unit fibre and a unit local cell, so neither local WZ packing nor unit
branching can bound their number.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)
  (G : HierarchyRandomMotionGeometry H)
  (J : HierarchyJointRandomMotionCertificate H G)

/-! ## The literal level-zero parent partition -/

/-- Active parents of the honest first hierarchy step. -/
abbrev LevelZeroActiveParent (hdepth : 0 < depth) :=
  {p : Index 1 // p ∈ (H.step 0 hdepth).combinatorics.index.coarse}

/-- The actual number of active parents in the first hierarchy step. -/
def levelZeroParentCount (hdepth : 0 < depth) : Nat :=
  (H.step 0 hdepth).combinatorics.index.coarse.card

@[simp]
theorem card_levelZeroActiveParent (hdepth : 0 < depth) :
    Fintype.card (LevelZeroActiveParent H hdepth) =
      levelZeroParentCount H hdepth := by
  simp [LevelZeroActiveParent, levelZeroParentCount]

/-- One actual random-motion collision cell assigned to one honest active
level-zero parent.  Its membership field concerns only that parent's literal
hierarchy fibre. -/
structure LevelZeroParentCellCapture
    (hdepth : 0 < depth) (p : LevelZeroActiveParent H hdepth) where
  candidate : ModelCandidate
    (hierarchyCollisionGrid H G J (zeroLayer hdepth) p.1)
  repetition : Fin (repetitions G.toDependentSource (zeroLayer hdepth))
  contains_fiber : forall i : Index 0,
    i ∈ (H.step 0 hdepth).combinatorics.index.fiber p.1 ->
      i ∈ candidateCollisionFinset
        (hierarchyCollisionGrid H G J (zeroLayer hdepth) p.1)
        candidate
        ((J.output.layerOutput (zeroLayer hdepth)).omega repetition)

/-- A separate concrete cell capture for every active first-step parent. -/
structure LevelZeroParentPartitionCollisionCellCapture
    (hdepth : 0 < depth) where
  parentCell : forall p : LevelZeroActiveParent H hdepth,
    LevelZeroParentCellCapture H G J hdepth p

namespace LevelZeroParentCellCapture

variable {H C S G J} {hdepth : 0 < depth}
  {p : LevelZeroActiveParent H hdepth}
  (P : LevelZeroParentCellCapture H G J hdepth p)

/-- The exact selected hierarchy collision-cell subtype assigned to `p`. -/
abbrev CellIndex :=
  SelectedHierarchyCollisionCellIndex H G J (zeroLayer hdepth)
    p.1 P.candidate P.repetition

/-- The raw active-parent proof is definitionally the active-parent proof for
the actual hierarchy random-motion layer. -/
theorem parent_mem_layer :
    p.1 ∈ (G.toDependentSource.layer (zeroLayer hdepth)).activeParents := by
  change p.1 ∈ (H.step 0 hdepth).combinatorics.index.coarse
  exact p.2

/-- A parent's literal hierarchy fibre embeds by unchanged source index into
its own selected collision cell. -/
def parentFiberEmbedding :
    {i // i ∈ (H.step 0 hdepth).combinatorics.index.fiber p.1} ↪
      P.CellIndex where
  toFun := fun i => ⟨i.1, P.contains_fiber i.1 i.2⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x : P.CellIndex => x.1) hij

/-- Existing WZ separation and the literal common-`100 T` container cap this
parent's actual selected cell. -/
theorem cell_card_le_commonHundredNeighbourPackingConstant
    (W : HierarchyLevelWZSeparationData H) :
    Fintype.card P.CellIndex <= commonHundredNeighbourPackingConstant := by
  exact
    selectedHierarchyCollisionCell_card_le_commonHundredNeighbourPackingConstant
      H G J W (zeroLayer hdepth) p.1
        (parent_mem_layer (H := H) (G := G) (hdepth := hdepth) (p := p))
        P.candidate P.repetition

include P

/-- Therefore each literal first-step parent fibre has the WZ constant cap. -/
theorem parentFiber_card_le_commonHundredNeighbourPackingConstant
    (W : HierarchyLevelWZSeparationData H) :
    ((H.step 0 hdepth).combinatorics.index.fiber p.1).card <=
      commonHundredNeighbourPackingConstant := by
  have hcard := Fintype.card_le_of_embedding
    (parentFiberEmbedding (H := H) (G := G) (J := J)
      (hdepth := hdepth) (p := p) P)
  simpa only [Fintype.card_coe] using
    hcard.trans
      (cell_card_le_commonHundredNeighbourPackingConstant
        (H := H) (G := G) (J := J) (hdepth := hdepth) (p := p) P W)

end LevelZeroParentCellCapture

namespace LevelZeroParentPartitionCollisionCellCapture

variable {H C S G J} {hdepth : 0 < depth}
  (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)

include Z

/-- Summing the actual parent-fibre bounds along the hierarchy's literal
partition gives the exact parent-count times WZ-constant source cap. -/
theorem initialRefined_card_le_parentCount_mul_commonHundredNeighbourPackingConstant
    (W : HierarchyLevelWZSeparationData H) :
    (H.family 0).refinement.refined.card <=
      levelZeroParentCount H hdepth *
        commonHundredNeighbourPackingConstant := by
  rw [← (H.step 0 hdepth).combinatorics.fine_eq_refined,
    (H.step 0 hdepth).combinatorics.index.card_eq_sum_card_fiber]
  calc
    (∑ p ∈ (H.step 0 hdepth).combinatorics.index.coarse,
        ((H.step 0 hdepth).combinatorics.index.fiber p).card) <=
        ∑ _p ∈ (H.step 0 hdepth).combinatorics.index.coarse,
          commonHundredNeighbourPackingConstant := by
      exact Finset.sum_le_sum fun p hp =>
        LevelZeroParentCellCapture.parentFiber_card_le_commonHundredNeighbourPackingConstant
          (P := LevelZeroParentPartitionCollisionCellCapture.parentCell Z
            ⟨p, hp⟩) W
    _ = levelZeroParentCount H hdepth *
          commonHundredNeighbourPackingConstant := by
      simp [levelZeroParentCount]

end LevelZeroParentPartitionCollisionCellCapture

/-! ## Producing the parent-count occurrence loss -/

variable {H C S G J}

/-- Every actual lower-cover fibre embeds into the literal active initial
hierarchy source. -/
def lowerFiberInitialRefinedEmbedding
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (q : LowerActiveParent H C S m rho hTauRho hRhoTheta) :
    {i // i ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).fiber q.1} ↪
      {i // i ∈ (H.family 0).refinement.refined} where
  toFun := fun i => ⟨i.1, by
    let L := lowerScaleCover C S m rho hTauRho hRhoTheta
    have hiActive : i.1 ∈ L.activeFine :=
      ((L.mem_fiber i.1 q.1).1 i.2).1
    rw [L.activeFine_eq_refined] at hiActive
    exact hiActive⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg
      (fun x : {i // i ∈ (H.family 0).refinement.refined} => x.1) hij

/-- Generic finite step used only after a geometric source-cardinality bound
has been derived: a bounded active initial source supplies a sibling
occurrence code with the same loss. -/
def siblingOccurrenceCodeOfInitialRefinedCardBound
    (cardLoss : Nat)
    (hbound : Fintype.card {i // i ∈ (H.family 0).refinement.refined} <=
      cardLoss) :
    SiblingOccurrenceCode H C S cardLoss where
  fiberEmbedding := by
    intro m rho hTauRho hRhoTheta k hk q
    let L := lowerScaleCover C S m rho hTauRho hRhoTheta
    have hsource : Fintype.card {i // i ∈ L.fiber q.1} <= cardLoss :=
      (Fintype.card_le_of_embedding
        (lowerFiberInitialRefinedEmbedding (H := H) (C := C) (S := S)
          m rho hTauRho hRhoTheta
          (lowerActiveOfSibling H C S m rho hTauRho hRhoTheta k q))).trans
        hbound
    have hnonempty : (L.fiber k).Nonempty :=
      activeCoarse_fiber_nonempty L k hk
    have hpos : 0 < (L.fiber k).card := Finset.card_pos.mpr hnonempty
    have hcard :
        Fintype.card {i // i ∈ L.fiber q.1} <=
          Fintype.card (Fin cardLoss × {i // i ∈ L.fiber k}) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
        hsource.trans (Nat.le_mul_of_pos_right cardLoss hpos)
    exact (Function.Embedding.nonempty_of_card_le hcard).some

/-- The parent-partition capture constructs the occurrence code with loss
`parentCount * commonHundredNeighbourPackingConstant`. -/
def parentPartitionSiblingOccurrenceCode
    {hdepth : 0 < depth}
    (W : HierarchyLevelWZSeparationData H)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth) :
    SiblingOccurrenceCode H C S
      (levelZeroParentCount H hdepth *
        commonHundredNeighbourPackingConstant) := by
  apply siblingOccurrenceCodeOfInitialRefinedCardBound (H := H) (C := C) (S := S)
  simpa only [Fintype.card_coe] using
    Z.initialRefined_card_le_parentCount_mul_commonHundredNeighbourPackingConstant W

/-! ## Reverse normalizer and Sticky endpoint -/

/-- Parent nesting and the parent-partitioned collision cells produce the
complete sibling-rigidity certificate. -/
def parentPartitionSelectedNestedSiblingRigidityCertificate
    {hdepth : 0 < depth}
    (W : HierarchyLevelWZSeparationData H)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth) :
    HierarchySiblingRigidityCertificate H C S
      (hierarchyBranchingBound H)
      (16 *
        ((levelZeroParentCount H hdepth *
          commonHundredNeighbourPackingConstant : Nat) : ENNReal)) :=
  hierarchySiblingRigidityCertificate hhalf R.toParentSquareIdentification
    (parentPartitionSiblingOccurrenceCode W Z)

/-- Actual reverse-parent loss with separate collision cells for separate
level-zero hierarchy parents. -/
theorem actualReverseParentNormalizerLoss_le_of_parentPartitionCollisionCells
    {hdepth : 0 < depth}
    (W : HierarchyLevelWZSeparationData H)
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
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
  exact actualReverseParentNormalizerLoss_le_of_parentSquare_occurrenceCode
    hdelta hhalf R.toParentSquareIdentification
      (parentPartitionSiblingOccurrenceCode W Z) hcompat

/-- Arbitrary-radius Sticky with the honest parent-count times common-`100 T`
occurrence factor. -/
theorem isStickyAtEveryScale_of_parentPartitionCollisionCells
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
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth) :
    C.base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
          (16 *
            ((levelZeroParentCount H hdepth *
              commonHundredNeighbourPackingConstant : Nat) : ENNReal)) *
        frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_parentSquare_occurrenceCode
    hdepth hdelta hhalf D B R.toParentSquareIdentification
      (parentPartitionSiblingOccurrenceCode W Z)

/-! ## Optional fixed parent code and the sharp obstruction -/

/-- The minimal finite datum which can replace the actual hierarchy parent
count by a fixed `parentLoss`: an injection of the real active parent subtype,
not an unrelated numeric cap. -/
structure LevelZeroParentCode (hdepth : 0 < depth) (parentLoss : Nat) where
  parentEmbedding : LevelZeroActiveParent H hdepth ↪ Fin parentLoss

namespace LevelZeroParentCode

variable {hdepth : 0 < depth} {parentLoss : Nat}
  (P : LevelZeroParentCode (H := H) hdepth parentLoss)

include P
theorem parentCount_le :
    levelZeroParentCount H hdepth <= parentLoss := by
  have hcard := Fintype.card_le_of_embedding P.parentEmbedding
  simpa only [card_levelZeroActiveParent, Fintype.card_fin] using hcard

end LevelZeroParentCode

variable {hdepth : 0 < depth} {parentLoss : Nat}

/-- Combining a real parent code with the per-parent WZ cells gives the
further compressed occurrence code. -/
def encodedParentPartitionSiblingOccurrenceCode
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (W : HierarchyLevelWZSeparationData H)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth) :
    SiblingOccurrenceCode H C S
      (parentLoss * commonHundredNeighbourPackingConstant) := by
  apply siblingOccurrenceCodeOfInitialRefinedCardBound (H := H) (C := C) (S := S)
  simpa only [Fintype.card_coe] using
    (Z.initialRefined_card_le_parentCount_mul_commonHundredNeighbourPackingConstant W).trans
      (Nat.mul_le_mul_right commonHundredNeighbourPackingConstant
        (LevelZeroParentCode.parentCount_le P))

/-- Conditional reverse endpoint under the exact additional parent code. -/
theorem actualReverseParentNormalizerLoss_le_of_encodedParentPartition
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (W : HierarchyLevelWZSeparationData H)
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (hcompat : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : Index 0),
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    actualReverseParentNormalizerLoss C S <=
      hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
        (16 * ((parentLoss * commonHundredNeighbourPackingConstant : Nat) :
          ENNReal)) := by
  exact actualReverseParentNormalizerLoss_le_of_parentSquare_occurrenceCode
    hdelta hhalf R.toParentSquareIdentification
      (encodedParentPartitionSiblingOccurrenceCode P W Z) hcompat

/-- Conditional Sticky endpoint under the same genuine parent embedding. -/
theorem isStickyAtEveryScale_of_encodedParentPartition
    {epsilon : Real}
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    (W : HierarchyLevelWZSeparationData H)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth) :
    C.base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
          (16 * ((parentLoss * commonHundredNeighbourPackingConstant : Nat) :
            ENNReal)) * frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_parentSquare_occurrenceCode
    hdepth hdelta hhalf D B R.toParentSquareIdentification
      (encodedParentPartitionSiblingOccurrenceCode P W Z)

/-- Arbitrarily many parents may all have unit branching and unit local-cell
cardinality.  Hence local branching/WZ bounds cannot produce a uniform parent
code. -/
theorem unit_parent_fibres_do_not_bound_parentCount (K : Nat) :
    (forall _p : Fin (K + 1), Fintype.card (Fin 1) <= 1) ∧
      Not (Nonempty (Fin (K + 1) ↪ Fin K)) := by
  constructor
  · intro _p
    simp
  · intro h
    obtain ⟨E⟩ := h
    have hcard := Fintype.card_le_of_embedding E
    norm_num at hcard

/-- The same obstruction on the full parent-by-unit-cell source: aggregating
locally bounded cells necessarily pays the number of parents. -/
theorem no_fixed_totalSourceCode_from_unit_parent_cells (K : Nat) :
    Not (Nonempty ((Fin (K + 1) × Fin 1) ↪ Fin K)) := by
  intro h
  obtain ⟨E⟩ := h
  have hcard := Fintype.card_le_of_embedding E
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  omega

#print axioms card_levelZeroActiveParent
#print axioms LevelZeroParentCellCapture.parent_mem_layer
#print axioms LevelZeroParentCellCapture.parentFiberEmbedding
#print axioms LevelZeroParentCellCapture.cell_card_le_commonHundredNeighbourPackingConstant
#print axioms LevelZeroParentCellCapture.parentFiber_card_le_commonHundredNeighbourPackingConstant
#print axioms LevelZeroParentPartitionCollisionCellCapture.initialRefined_card_le_parentCount_mul_commonHundredNeighbourPackingConstant
#print axioms lowerFiberInitialRefinedEmbedding
#print axioms siblingOccurrenceCodeOfInitialRefinedCardBound
#print axioms parentPartitionSiblingOccurrenceCode
#print axioms parentPartitionSelectedNestedSiblingRigidityCertificate
#print axioms actualReverseParentNormalizerLoss_le_of_parentPartitionCollisionCells
#print axioms isStickyAtEveryScale_of_parentPartitionCollisionCells
#print axioms LevelZeroParentCode.parentCount_le
#print axioms encodedParentPartitionSiblingOccurrenceCode
#print axioms actualReverseParentNormalizerLoss_le_of_encodedParentPartition
#print axioms isStickyAtEveryScale_of_encodedParentPartition
#print axioms unit_parent_fibres_do_not_bound_parentCount
#print axioms no_fixed_totalSourceCode_from_unit_parent_cells

end
end FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1
