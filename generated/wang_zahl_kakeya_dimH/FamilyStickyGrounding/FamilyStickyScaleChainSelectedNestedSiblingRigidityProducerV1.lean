import FamilyStickyGrounding.FamilyStickyScaleChainHierarchySiblingRigidityProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainSelectedNestedSiblingRigidityProducerV1

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

noncomputable section

/-!
# Selected nested hierarchy input for sibling rigidity

The repository's selected hierarchy recursively retains the literal images
of selected children under each honest hierarchy parent map.  This module
uses that concrete recursion to reduce the missing parent square to one raw
lower-occurrence realization:

* actual lower cover parents embed in the recursively selected hierarchy
  children at the corresponding layer;
* equality of actual cross-scale parents is equivalent to equality of the
  honest hierarchy parents of their images.

Surjectivity of the real cross-scale cover then constructs, rather than
assumes, the upper-parent embedding and its commuting square.

The second input needs no extra data for a finite family.  Every lower fiber
embeds into the full level-zero occurrence type, while every distinguished
active fiber is nonempty.  Consequently an occurrence code with loss
`Fintype.card (Index 0)` is automatic.  Tube-volume uniformity upgrades it to
the mass loss `16 * Fintype.card (Index 0)`.  This is a genuine finite
closure, but not an absolute paper constant; the final obstruction shows
why the present hierarchy fields cannot make that loss uniform in the input
family.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)

/-! ## The one remaining raw selected-nesting interface -/
/-- Starting with selected level-zero occurrences, recursively retain their
literal images under the honest hierarchy parent maps. -/
def nestedLevelIndices (selected : Finset (Index 0)) :
    (l : Nat) -> Finset (Index l)
  | 0 => selected
  | l + 1 =>
      if hl : l < depth then
        (nestedLevelIndices selected l).image (H.step l hl).parentIndex
      else
        ∅

@[simp]
theorem nestedLevelIndices_zero (selected : Finset (Index 0)) :
    nestedLevelIndices H selected 0 = selected :=
  rfl

theorem nestedLevelIndices_succ (selected : Finset (Index 0))
    (l : Nat) (hl : l < depth) :
    nestedLevelIndices H selected (l + 1) =
      (nestedLevelIndices H selected l).image
        (H.step l hl).parentIndex := by
  simp [nestedLevelIndices, hl]

/-- Every recursively selected occurrence remains in the literal active
refinement of its hierarchy level. -/
theorem nestedLevelIndices_subset_refined
    {selected : Finset (Index 0)}
    (hselected : selected ⊆ (H.family 0).refinement.refined)
    (l : Nat) (hl : l <= depth) :
    nestedLevelIndices H selected l ⊆
      (H.family l).refinement.refined := by
  induction l with
  | zero => simpa using hselected
  | succ l ih =>
      have hlt : l < depth := by omega
      rw [nestedLevelIndices_succ H selected l hlt]
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      have hiFine : i ∈ (H.step l hlt).combinatorics.index.fine := by
        rw [(H.step l hlt).combinatorics.fine_eq_refined]
        exact ih (by omega) hi
      have hpCoarse := (H.step l hlt).parentIndex_mem hiFine
      rw [(H.step l hlt).combinatorics.coarse_eq_refined] at hpCoarse
      exact hpCoarse


/-- Actual occurrences retained at a recursively selected hierarchy level. -/
abbrev SelectedLevelIndex (selected : Finset (Index 0)) (l : Nat) :=
  {i // i ∈ nestedLevelIndices H selected l}

/--
The minimal lower-occurrence realization needed from a concrete cover
construction.  No upper map is stored.  The `parent_eq_iff` field says that
the partition of lower occurrences into actual cross-scale fibers is exactly
the partition induced by the honest hierarchy parent map after embedding.

The selected sets and hierarchy parents here are the literal definitions
from `FamilyStickyHierarchySelectedSourceNestedRestrictionV1` and
`MultiscaleTubeHierarchy`, not replacement callbacks.
-/
structure SelectedNestedParentRealization
    (selected : Finset (Index 0)) where
  selected_subset_refined :
    selected ⊆ (H.family 0).refinement.refined
  lowerEmbedding : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    LowerActiveParent H C S m rho hTauRho hRhoTheta ↪
      SelectedLevelIndex H selected m.1
  parent_eq_iff : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (q q' : LowerActiveParent H C S m rho hTauRho hRhoTheta),
    crossParentOfLower H C S m rho hTauRho hRhoTheta q =
        crossParentOfLower H C S m rho hTauRho hRhoTheta q' ↔
      (H.step m.1 m.2).parentIndex
          ((lowerEmbedding m rho hTauRho hRhoTheta q).1) =
        (H.step m.1 m.2).parentIndex
          ((lowerEmbedding m rho hTauRho hRhoTheta q').1)

/-! ## Constructing the missing upper map from real cover surjectivity -/

/-- Every active endpoint parent is hit by an actual lower active parent. -/
theorem crossParentOfLower_surjective
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    Function.Surjective
      (crossParentOfLower H C S m rho hTauRho hRhoTheta) := by
  intro p
  let I := rhoToUpperCover C S m rho hTauRho hRhoTheta
  obtain ⟨q, hq, hqp⟩ := I.parent_surjective p.1 p.2
  refine ⟨⟨q, ?_⟩, ?_⟩
  · exact hq
  · apply Subtype.ext
    exact hqp

/-- A fixed preimage supplied by the genuine cross-scale surjectivity. -/
def chosenLowerOfUpper
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (p : UpperActiveParent H C S m) :
    LowerActiveParent H C S m rho hTauRho hRhoTheta :=
  Classical.choose
    (crossParentOfLower_surjective H C S m rho hTauRho hRhoTheta p)

@[simp]
theorem crossParent_chosenLowerOfUpper
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (p : UpperActiveParent H C S m) :
    crossParentOfLower H C S m rho hTauRho hRhoTheta
        (chosenLowerOfUpper H C S m rho hTauRho hRhoTheta p) = p :=
  Classical.choose_spec
    (crossParentOfLower_surjective H C S m rho hTauRho hRhoTheta p)

namespace SelectedNestedParentRealization

variable {H C S} {selected : Finset (Index 0)}
  (R : SelectedNestedParentRealization H C S selected)

/-- The honest hierarchy parent of the selected preimage of an upper cover
parent.  Recursive selected nesting proves that it lies at the next selected
level. -/
def nestedParentOfUpper
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (p : UpperActiveParent H C S m) :
    SelectedLevelIndex H selected (m.1 + 1) := by
  let q := chosenLowerOfUpper H C S m rho hTauRho hRhoTheta p
  let i := R.lowerEmbedding m rho hTauRho hRhoTheta q
  refine ⟨(H.step m.1 m.2).parentIndex i.1, ?_⟩
  rw [nestedLevelIndices_succ H selected m.1 m.2]
  exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩

/-- Parent reflection in the raw realization makes the induced upper map
injective. -/
theorem nestedParentOfUpper_injective
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    Function.Injective
      (R.nestedParentOfUpper m rho hTauRho hRhoTheta) := by
  intro p p' hpp'
  let q := chosenLowerOfUpper H C S m rho hTauRho hRhoTheta p
  let q' := chosenLowerOfUpper H C S m rho hTauRho hRhoTheta p'
  have hparent :
      (H.step m.1 m.2).parentIndex
          ((R.lowerEmbedding m rho hTauRho hRhoTheta q).1) =
        (H.step m.1 m.2).parentIndex
          ((R.lowerEmbedding m rho hTauRho hRhoTheta q').1) := by
    exact congrArg
      (fun x : SelectedLevelIndex H selected (m.1 + 1) => x.1) hpp'
  have hcross :=
    (R.parent_eq_iff m rho hTauRho hRhoTheta q q').2 hparent
  calc
    p = crossParentOfLower H C S m rho hTauRho hRhoTheta q := by
      exact (crossParent_chosenLowerOfUpper H C S
        m rho hTauRho hRhoTheta p).symm
    _ = crossParentOfLower H C S m rho hTauRho hRhoTheta q' := hcross
    _ = p' := crossParent_chosenLowerOfUpper H C S
      m rho hTauRho hRhoTheta p'

/-- Forgetting the selected-level proof gives an embedding into the literal
fine side of the real hierarchy step. -/
def lowerStepEmbedding
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    LowerActiveParent H C S m rho hTauRho hRhoTheta ↪
      {i // i ∈ (H.step m.1 m.2).combinatorics.index.fine} where
  toFun := fun q => ⟨
    (R.lowerEmbedding m rho hTauRho hRhoTheta q).1,
    by
      rw [(H.step m.1 m.2).combinatorics.fine_eq_refined]
      exact nestedLevelIndices_subset_refined H
        R.selected_subset_refined m.1 (Nat.le_of_lt m.2)
          (R.lowerEmbedding m rho hTauRho hRhoTheta q).2⟩
  inj' := by
    intro q q' hqq'
    apply (R.lowerEmbedding m rho hTauRho hRhoTheta).injective
    apply Subtype.ext
    have hval := congrArg (fun x => x.1) hqq'
    exact hval

/-- Forgetting the selected-level proof gives the derived upper embedding
into the literal coarse side of the same hierarchy step. -/
def upperStepEmbedding
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    UpperActiveParent H C S m ↪
      {p // p ∈ (H.step m.1 m.2).combinatorics.index.coarse} where
  toFun := fun p => ⟨
    (R.nestedParentOfUpper m rho hTauRho hRhoTheta p).1,
    by
      rw [(H.step m.1 m.2).combinatorics.coarse_eq_refined]
      exact nestedLevelIndices_subset_refined H
        R.selected_subset_refined (m.1 + 1)
          (Nat.succ_le_iff.mpr m.2)
          (R.nestedParentOfUpper m rho hTauRho hRhoTheta p).2⟩
  inj' := by
    intro p p' hpp'
    apply R.nestedParentOfUpper_injective m rho hTauRho hRhoTheta
    apply Subtype.ext
    have hval := congrArg (fun x => x.1) hpp'
    exact hval
/-- The induced upper embedding makes the honest hierarchy parent square
commute for every actual lower cover parent. -/
theorem parentIndex_lower_eq_nestedParent
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (q : LowerActiveParent H C S m rho hTauRho hRhoTheta) :
    (H.step m.1 m.2).parentIndex
        ((R.lowerStepEmbedding m rho hTauRho hRhoTheta q).1) =
      (R.upperStepEmbedding m rho hTauRho hRhoTheta
        (crossParentOfLower H C S m rho hTauRho hRhoTheta q)).1 := by
  let q' := chosenLowerOfUpper H C S m rho hTauRho hRhoTheta
    (crossParentOfLower H C S m rho hTauRho hRhoTheta q)
  have hcross :
      crossParentOfLower H C S m rho hTauRho hRhoTheta q =
        crossParentOfLower H C S m rho hTauRho hRhoTheta q' := by
    exact (crossParent_chosenLowerOfUpper H C S m rho hTauRho hRhoTheta
      (crossParentOfLower H C S m rho hTauRho hRhoTheta q)).symm
  exact (R.parent_eq_iff m rho hTauRho hRhoTheta q q').1 hcross

/-- The selected nested lower realization automatically produces the full
parent square required by sibling rigidity. -/
def toParentSquareIdentification :
    ParentSquareIdentification H C S where
  lowerEmbedding := R.lowerStepEmbedding
  upperEmbedding := R.upperStepEmbedding
  parent_commutes := R.parentIndex_lower_eq_nestedParent

end SelectedNestedParentRealization

/-! ## Automatic finite occurrence code -/

/-- Every distinguished active cover parent has a nonempty literal fine
fiber. -/
theorem activeCoarse_fiber_nonempty
    {delta r : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (T : StickyScaleCover fine r) (k : Fin T.coarseCard)
    (hk : k ∈ T.activeCoarse) : (T.fiber k).Nonempty := by
  obtain ⟨i, hi, hip⟩ := T.parent_surjective k hk
  exact ⟨i, (T.mem_fiber i k).2 ⟨hi, hip⟩⟩

/-- Pure finiteness supplies an occurrence code with the transparent ambient
loss `card (Index 0)`.  The target's distinguished-fiber factor is nonempty,
so it can store an embedding of every subtype of `Index 0`. -/
def ambientSiblingOccurrenceCode :
    SiblingOccurrenceCode H C S (Fintype.card (Index 0)) where
  fiberEmbedding := by
    intro m rho hTauRho hRhoTheta k hk q
    let L := lowerScaleCover C S m rho hTauRho hRhoTheta
    have hsource :
        Fintype.card {i // i ∈ L.fiber q.1} <= Fintype.card (Index 0) :=
      Fintype.card_le_of_injective
        (fun i : {i // i ∈ L.fiber q.1} => i.1) Subtype.val_injective
    have hnonempty : (L.fiber k).Nonempty :=
      activeCoarse_fiber_nonempty L k hk
    have hpos : 0 < (L.fiber k).card := Finset.card_pos.mpr hnonempty
    have hcard :
        Fintype.card {i // i ∈ L.fiber q.1} <=
          Fintype.card
            (Fin (Fintype.card (Index 0)) × {i // i ∈ L.fiber k}) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
        hsource.trans
          (Nat.le_mul_of_pos_right (Fintype.card (Index 0)) hpos)
    exact (Function.Embedding.nonempty_of_card_le hcard).some

/-! ## Closed reverse-normalizer and arbitrary-radius endpoint -/

/-- The selected nested realization is now the only extra structural input:
the occurrence code is computed internally. -/
def selectedNestedHierarchySiblingRigidityCertificate
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected) :
    HierarchySiblingRigidityCertificate H C S
      (hierarchyBranchingBound H)
      (16 * (Fintype.card (Index 0) : ENNReal)) :=
  hierarchySiblingRigidityCertificate hhalf
    R.toParentSquareIdentification (ambientSiblingOccurrenceCode H C S)

/-- Actual reverse-parent loss with both sibling-rigidity inputs produced
upstream. -/
theorem actualReverseParentNormalizerLoss_le_of_selectedNestedRealization
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected)
    (hcompat : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : Index 0),
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    actualReverseParentNormalizerLoss C S <=
      hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
        (16 * (Fintype.card (Index 0) : ENNReal)) := by
  exact actualReverseParentNormalizerLoss_le_of_parentSquare_occurrenceCode
    hdelta hhalf R.toParentSquareIdentification
      (ambientSiblingOccurrenceCode H C S) hcompat

/-- End-to-end arbitrary-radius Sticky, with the finite ambient occurrence
loss shown explicitly. -/
theorem isStickyAtEveryScale_of_selectedNestedRealization
    {epsilon : Real}
    (hdepth : 0 < depth) (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    {selected : Finset (Index 0)}
    (R : SelectedNestedParentRealization H C S selected) :
    C.base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
          (16 * (Fintype.card (Index 0) : ENNReal)) * frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_parentSquare_occurrenceCode
    hdepth hdelta hhalf D B R.toParentSquareIdentification
      (ambientSiblingOccurrenceCode H C S)

/-! ## Exact finite obstructions in the remaining seam -/

/-- Parent preservation without reflection cannot produce an injective upper
map.  Here all bodies may be identical, actual cover parents distinguish two
occurrences, and the hierarchy parent collapses both. -/
theorem preservation_without_reflection_blocks_upper_embedding :
    let body : Fin 2 -> Unit := fun _ => ()
    let coverParent : Fin 2 -> Fin 2 := fun i => i
    let hierarchyParent : Fin 2 -> Fin 1 := fun _ => 0
    (forall i, body i = body i) ∧
      (forall i j, coverParent i = coverParent j ->
        hierarchyParent i = hierarchyParent j) ∧
      ¬ Nonempty (Fin 2 ↪ Fin 1) := by
  dsimp
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro _ _ _
    rfl
  · intro h
    obtain ⟨E⟩ := h
    have hcard := Fintype.card_le_of_embedding E
    norm_num at hcard

/-- The automatic ambient occurrence loss cannot be replaced by a fixed
constant using finiteness or two-child branching alone. -/
theorem no_absolute_occurrence_loss_from_finiteness (K : Nat) :
    ¬ Nonempty (Fin (K + 1) ↪ Fin K × Fin 1) :=
  no_fixed_occurrence_code_for_two_siblings K

#print axioms nestedLevelIndices
#print axioms nestedLevelIndices_subset_refined
#print axioms crossParentOfLower_surjective
#print axioms crossParent_chosenLowerOfUpper
#print axioms SelectedNestedParentRealization.nestedParentOfUpper_injective
#print axioms SelectedNestedParentRealization.lowerStepEmbedding
#print axioms SelectedNestedParentRealization.upperStepEmbedding
#print axioms SelectedNestedParentRealization.parentIndex_lower_eq_nestedParent
#print axioms SelectedNestedParentRealization.toParentSquareIdentification
#print axioms activeCoarse_fiber_nonempty
#print axioms ambientSiblingOccurrenceCode
#print axioms selectedNestedHierarchySiblingRigidityCertificate
#print axioms actualReverseParentNormalizerLoss_le_of_selectedNestedRealization
#print axioms isStickyAtEveryScale_of_selectedNestedRealization
#print axioms preservation_without_reflection_blocks_upper_embedding
#print axioms no_absolute_occurrence_loss_from_finiteness

end
end FamilyStickyScaleChainSelectedNestedSiblingRigidityProducerV1
