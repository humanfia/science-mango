import FamilyStickyGrounding.FamilyStickyHierarchyTerminalSourceChartBucketProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set
open scoped NNReal BigOperators

namespace FamilyStickyHierarchySelectedSourceNestedRestrictionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyRandomFiniteMaximalCellCodeV1
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyTerminalCarrierDedupV1
open FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1
open FamilyStickyHierarchyTerminalWZ2CoefficientBridgeV1
open FamilyStickyHierarchyTerminalSameScaleCoverProducerV1
open FamilyStickyHierarchyTerminalSourceChartBucketProducerV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Restricting a hierarchy and its terminal family to a selected source

This module starts with an honest
`SelectedTerminalSourceChartBucketGeometry`.  It never identifies the
selected indices with the original level-zero refinement.

There are two complementary adapters.

* At the hierarchy level, selected parents are generated recursively as the
  images of selected children.  Every adjacent step is genuinely restricted
  to subtypes.  Its upper branching factor is kept equal to the old one, and
  the constructor kind (`partition` or `commonFine`) is preserved, so all
  effective radii remain unchanged.
* For an already constructed joint random-motion certificate, the old path
  choices are paired only with selected source indices.  A new maximal strong
  selection on this restricted occurrence type supplies the pairwise WZ2
  family consumed by the generic terminal coefficient bridge.

The old joint output itself is not cast to the rebuilt hierarchy: its layer
repetition types depend on the full parent fibers.  The exact transport data
missing for such a cast is recorded at the end.
-/

universe u v

/-! ## Restriction of one adjacent hierarchy step -/

namespace RestrictedStep

variable {r R : NNReal} {iota kappa : Type*}
  [Fintype iota] [DecidableEq iota]
  [Fintype kappa] [DecidableEq kappa]
  {child : UniformTubeFamily r iota}
  {parent : UniformTubeFamily R kappa}

/-- Active parents actually hit by a selected child set. -/
def restrictedParents (A : AdjacentTubeStep child parent)
    (selected : Finset iota) : Finset kappa :=
  selected.image A.parentIndex

abbrev RestrictedChildIndex
    (_A : AdjacentTubeStep child parent) (selected : Finset iota) :=
  {i // i ∈ selected}

abbrev RestrictedParentIndex
    (A : AdjacentTubeStep child parent) (selected : Finset iota) :=
  {p // p ∈ restrictedParents A selected}

/-- The old parent map restricted to the selected subtype and its literal
image. -/
def restrictedParentIndex
    (A : AdjacentTubeStep child parent) (selected : Finset iota)
    (i : RestrictedChildIndex A selected) :
    RestrictedParentIndex A selected :=
  ⟨A.parentIndex i.1,
    Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩

/-- The finite factorization on the selected child subtype. -/
def restrictedIndexFactorization
    (A : AdjacentTubeStep child parent) (selected : Finset iota) :
    IndexFactorization (RestrictedChildIndex A selected)
      (RestrictedParentIndex A selected) where
  fine := Finset.univ
  coarse := Finset.univ
  parent := restrictedParentIndex A selected
  parent_mem := by simp

theorem restrictedParents_nonempty
    (A : AdjacentTubeStep child parent) {selected : Finset iota}
    (hselected : selected.Nonempty) :
    (restrictedParents A selected).Nonempty :=
  hselected.image A.parentIndex

theorem restrictedIndexFactorization_parent_surjective
    (A : AdjacentTubeStep child parent) {selected : Finset iota}
    (p : RestrictedParentIndex A selected) :
    ∃ i ∈ (restrictedIndexFactorization A selected).fine,
      (restrictedIndexFactorization A selected).parent i = p := by
  obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp p.2
  let i' : RestrictedChildIndex A selected := ⟨i, hi⟩
  refine ⟨i', Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  exact hip

/-- Forgetting subtype proofs maps a selected parent fiber injectively into
the corresponding original fiber. -/
theorem restrictedFiber_val_image_subset_originalFiber
    (A : AdjacentTubeStep child parent) {selected : Finset iota}
    (hselected : selected ⊆ A.combinatorics.index.fine)
    (p : RestrictedParentIndex A selected) :
    ((restrictedIndexFactorization A selected).fiber p).image Subtype.val ⊆
      A.combinatorics.index.fiber p.1 := by
  intro i hi
  obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
  have hifiber :=
    ((restrictedIndexFactorization A selected).mem_fiber i' p).mp hi'
  apply (A.combinatorics.index.mem_fiber i'.1 p.1).mpr
  exact ⟨hselected i'.2,
    congrArg Subtype.val hifiber.2⟩

theorem restrictedFiber_card_le_originalFiber
    (A : AdjacentTubeStep child parent) {selected : Finset iota}
    (hselected : selected ⊆ A.combinatorics.index.fine)
    (p : RestrictedParentIndex A selected) :
    ((restrictedIndexFactorization A selected).fiber p).card ≤
      (A.combinatorics.index.fiber p.1).card := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  exact Finset.card_le_card
    (restrictedFiber_val_image_subset_originalFiber A hselected p)

theorem restrictedFiber_nonempty
    (A : AdjacentTubeStep child parent) {selected : Finset iota}
    (p : RestrictedParentIndex A selected) :
    ((restrictedIndexFactorization A selected).fiber p).Nonempty := by
  obtain ⟨i, _hi, hip⟩ :=
    restrictedIndexFactorization_parent_surjective A p
  exact ⟨i,
    ((restrictedIndexFactorization A selected).mem_fiber i p).mpr
      ⟨Finset.mem_univ _, hip⟩⟩

theorem restrictedParent_val_mem_originalCoarse
    (A : AdjacentTubeStep child parent) {selected : Finset iota}
    (hselected : selected ⊆ A.combinatorics.index.fine)
    (p : RestrictedParentIndex A selected) :
    p.1 ∈ A.combinatorics.index.coarse := by
  obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp p.2
  rw [← hip]
  exact A.combinatorics.index.parent_mem i (hselected hi)

/-- Restrict the combinatorics without worsening the old upper branching
factor.  The target branching is one; the old branching factor is the new
loss, so every nonempty restricted fiber satisfies both sides. -/
def restrictCombinatorics
    (A : AdjacentTubeStep child parent) (selected : Finset iota)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine) :
    TubePartitionCombinatorics
      (child.restrictTo selected)
      (parent.restrictTo (restrictedParents A selected)) where
  scale_le := A.combinatorics.scale_le
  index := restrictedIndexFactorization A selected
  fine_eq_refined := rfl
  coarse_eq_refined := rfl
  coarse_nonempty := by
    obtain ⟨p, hp⟩ := restrictedParents_nonempty A hselected_nonempty
    exact ⟨⟨p, hp⟩, Finset.mem_univ _⟩
  parent_surjective := by
    intro p _hp
    exact restrictedIndexFactorization_parent_surjective A p
  branching := 1
  branching_pos := by norm_num
  branchingLoss := A.combinatorics.branchingFactor
  branchingLoss_pos := Nat.mul_pos A.combinatorics.branchingLoss_pos
    A.combinatorics.branching_pos
  branching_le_loss_mul_fiber := by
    intro p _hp
    have hfactor : 0 < A.combinatorics.branchingFactor :=
      Nat.mul_pos A.combinatorics.branchingLoss_pos
        A.combinatorics.branching_pos
    have hfiber : 0 <
        ((restrictedIndexFactorization A selected).fiber p).card :=
      Finset.card_pos.mpr (restrictedFiber_nonempty A p)
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hfactor.ne' hfiber.ne')
  fiber_card_le_loss_mul_branching := by
    intro p _hp
    simpa [TubePartitionCombinatorics.branchingFactor] using
      (restrictedFiber_card_le_originalFiber A hselected p).trans
        (A.combinatorics.fiber_card_le_loss_mul_branching p.1
          (restrictedParent_val_mem_originalCoarse A hselected p))

/-- Restrict an exact partition while preserving every selected tube and its
original parent carrier containment. -/
def restrictPartition
    (P : CoarseTubePartition child parent) (selected : Finset iota)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ P.index.fine) :
    CoarseTubePartition
      (child.restrictTo selected)
      (parent.restrictTo (restrictedParents (.partition P) selected)) := by
  let A : AdjacentTubeStep child parent := .partition P
  let C := restrictCombinatorics A selected hselected_nonempty hselected
  exact {
    scale_le := C.scale_le
    index := C.index
    fine_eq_refined := C.fine_eq_refined
    coarse_eq_refined := C.coarse_eq_refined
    coarse_nonempty := C.coarse_nonempty
    carrier_subset := by
      intro i _hi
      exact P.carrier_subset i.1 (hselected i.2)
    parent_surjective := C.parent_surjective
    branching := C.branching
    branching_pos := C.branching_pos
    branchingLoss := C.branchingLoss
    branchingLoss_pos := C.branchingLoss_pos
    branching_le_loss_mul_fiber := C.branching_le_loss_mul_fiber
    fiber_card_le_loss_mul_branching := C.fiber_card_le_loss_mul_branching }

/-- Restrict common-fine cover data by reusing each selected child witness. -/
def restrictCommonFine
    (D : CommonFineTubeCoverData child parent) (selected : Finset iota)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ D.combinatorics.index.fine) :
    CommonFineTubeCoverData
      (child.restrictTo selected)
      (parent.restrictTo
        (restrictedParents (.commonFine D) selected)) := by
  let A : AdjacentTubeStep child parent := .commonFine D
  let C := restrictCombinatorics A selected hselected_nonempty hselected
  exact {
    combinatorics := C
    commonFine := by
      intro i _hi
      exact D.commonFine i.1 (hselected i.2) }

/-- Genuine restriction of either adjacent-step constructor.  Preserving the
constructor is essential: it preserves `rawCost`, hence all accumulated
buffers in the recursive hierarchy below. -/
def restrict
    (A : AdjacentTubeStep child parent) (selected : Finset iota)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine) :
    AdjacentTubeStep
      (child.restrictTo selected)
      (parent.restrictTo (restrictedParents A selected)) := by
  cases A with
  | partition P =>
      exact .partition (restrictPartition P selected hselected_nonempty hselected)
  | commonFine D =>
      exact .commonFine (restrictCommonFine D selected hselected_nonempty hselected)

@[simp]
theorem restrict_rawCost
    (A : AdjacentTubeStep child parent) (selected : Finset iota)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine) :
    (restrict A selected hselected_nonempty hselected).rawCost = A.rawCost := by
  cases A <;> rfl

@[simp]
theorem restrict_branchingFactor
    (A : AdjacentTubeStep child parent) (selected : Finset iota)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine) :
    (restrict A selected hselected_nonempty hselected).combinatorics.branchingFactor =
      A.combinatorics.branchingFactor := by
  cases A with
  | partition P =>
      change (P.branchingLoss * P.branching) * 1 =
        P.branchingLoss * P.branching
      simp
  | commonFine D =>
      change (D.combinatorics.branchingLoss * D.combinatorics.branching) * 1 =
        D.combinatorics.branchingLoss * D.combinatorics.branching
      simp

end RestrictedStep

/-! ## Restriction to a propositionally specified parent image

The recursive level set below is propositionally, but not definitionally, the
literal `Finset.image` used by `RestrictedStep.restrict`.  Since the subtype's
finite instances depend on that finset, transporting the complete adjacent
step through a finset equality would introduce a brittle dependent cast.  The
following version instead accepts the intended parent finset together with
the exact image-membership equivalence. -/

namespace RestrictedStep.ToParentSet

variable {r R : NNReal} {iota kappa : Type*}
  [Fintype iota] [DecidableEq iota]
  [Fintype kappa] [DecidableEq kappa]
  {child : UniformTubeFamily r iota}
  {parent : UniformTubeFamily R kappa}

abbrev ChildIndex (_A : AdjacentTubeStep child parent)
    (selected : Finset iota) :=
  {i // i ∈ selected}

abbrev ParentIndex (_A : AdjacentTubeStep child parent)
    (parents : Finset kappa) :=
  {p // p ∈ parents}

def parentIndex (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (i : ChildIndex A selected) : ParentIndex A parents :=
  ⟨A.parentIndex i.1, (hparents _).2 ⟨i.1, i.2, rfl⟩⟩

def indexFactorization (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p) :
    IndexFactorization (ChildIndex A selected) (ParentIndex A parents) where
  fine := Finset.univ
  coarse := Finset.univ
  parent := parentIndex A selected parents hparents
  parent_mem := by simp

theorem parent_surjective (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (p : ParentIndex A parents) :
    ∃ i ∈ (indexFactorization A selected parents hparents).fine,
      (indexFactorization A selected parents hparents).parent i = p := by
  obtain ⟨i, hi, hip⟩ := (hparents p.1).mp p.2
  let i' : ChildIndex A selected := ⟨i, hi⟩
  refine ⟨i', Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  exact hip

theorem fiber_val_image_subset_originalFiber
    (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (hselected : selected ⊆ A.combinatorics.index.fine)
    (p : ParentIndex A parents) :
    ((indexFactorization A selected parents hparents).fiber p).image
        Subtype.val ⊆ A.combinatorics.index.fiber p.1 := by
  intro i hi
  obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
  have hifiber :=
    ((indexFactorization A selected parents hparents).mem_fiber i' p).mp hi'
  apply (A.combinatorics.index.mem_fiber i'.1 p.1).mpr
  exact ⟨hselected i'.2, congrArg Subtype.val hifiber.2⟩

theorem fiber_card_le_originalFiber
    (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (hselected : selected ⊆ A.combinatorics.index.fine)
    (p : ParentIndex A parents) :
    ((indexFactorization A selected parents hparents).fiber p).card ≤
      (A.combinatorics.index.fiber p.1).card := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  exact Finset.card_le_card
    (fiber_val_image_subset_originalFiber A selected parents hparents
      hselected p)

theorem fiber_nonempty (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (p : ParentIndex A parents) :
    ((indexFactorization A selected parents hparents).fiber p).Nonempty := by
  obtain ⟨i, _hi, hip⟩ := parent_surjective A selected parents hparents p
  exact ⟨i, ((indexFactorization A selected parents hparents).mem_fiber i p).mpr
    ⟨Finset.mem_univ _, hip⟩⟩

theorem parent_val_mem_originalCoarse
    (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (hselected : selected ⊆ A.combinatorics.index.fine)
    (p : ParentIndex A parents) :
    p.1 ∈ A.combinatorics.index.coarse := by
  obtain ⟨i, hi, hip⟩ := (hparents p.1).mp p.2
  rw [← hip]
  exact A.combinatorics.index.parent_mem i (hselected hi)

def combinatorics (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine) :
    TubePartitionCombinatorics
      (child.restrictTo selected) (parent.restrictTo parents) where
  scale_le := A.combinatorics.scale_le
  index := indexFactorization A selected parents hparents
  fine_eq_refined := rfl
  coarse_eq_refined := rfl
  coarse_nonempty := by
    obtain ⟨i, hi⟩ := hselected_nonempty
    let p : ParentIndex A parents :=
      ⟨A.parentIndex i, (hparents _).2 ⟨i, hi, rfl⟩⟩
    exact ⟨p, Finset.mem_univ _⟩
  parent_surjective := by
    intro p _hp
    exact parent_surjective A selected parents hparents p
  branching := 1
  branching_pos := by norm_num
  branchingLoss := A.combinatorics.branchingFactor
  branchingLoss_pos := Nat.mul_pos A.combinatorics.branchingLoss_pos
    A.combinatorics.branching_pos
  branching_le_loss_mul_fiber := by
    intro p _hp
    have hfactor : 0 < A.combinatorics.branchingFactor :=
      Nat.mul_pos A.combinatorics.branchingLoss_pos
        A.combinatorics.branching_pos
    have hfiber : 0 <
        ((indexFactorization A selected parents hparents).fiber p).card :=
      Finset.card_pos.mpr (fiber_nonempty A selected parents hparents p)
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hfactor.ne' hfiber.ne')
  fiber_card_le_loss_mul_branching := by
    intro p _hp
    simpa [TubePartitionCombinatorics.branchingFactor] using
      (fiber_card_le_originalFiber A selected parents hparents hselected p).trans
        (A.combinatorics.fiber_card_le_loss_mul_branching p.1
          (parent_val_mem_originalCoarse A selected parents hparents
            hselected p))

def partition (P : CoarseTubePartition child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, P.index.parent i = p)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ P.index.fine) :
    CoarseTubePartition
      (child.restrictTo selected) (parent.restrictTo parents) := by
  let A : AdjacentTubeStep child parent := .partition P
  let C := combinatorics A selected parents hparents
    hselected_nonempty hselected
  exact {
    scale_le := C.scale_le
    index := C.index
    fine_eq_refined := C.fine_eq_refined
    coarse_eq_refined := C.coarse_eq_refined
    coarse_nonempty := C.coarse_nonempty
    carrier_subset := by
      intro i _hi
      exact P.carrier_subset i.1 (hselected i.2)
    parent_surjective := C.parent_surjective
    branching := C.branching
    branching_pos := C.branching_pos
    branchingLoss := C.branchingLoss
    branchingLoss_pos := C.branchingLoss_pos
    branching_le_loss_mul_fiber := C.branching_le_loss_mul_fiber
    fiber_card_le_loss_mul_branching := C.fiber_card_le_loss_mul_branching }

def commonFine (D : CommonFineTubeCoverData child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, D.combinatorics.index.parent i = p)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ D.combinatorics.index.fine) :
    CommonFineTubeCoverData
      (child.restrictTo selected) (parent.restrictTo parents) := by
  let A : AdjacentTubeStep child parent := .commonFine D
  let C := combinatorics A selected parents hparents
    hselected_nonempty hselected
  exact {
    combinatorics := C
    commonFine := by
      intro i _hi
      exact D.commonFine i.1 (hselected i.2) }

def restrict (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine) :
    AdjacentTubeStep
      (child.restrictTo selected) (parent.restrictTo parents) := by
  cases A with
  | partition P =>
      exact .partition
        (partition P selected parents hparents hselected_nonempty hselected)
  | commonFine D =>
      exact .commonFine
        (commonFine D selected parents hparents hselected_nonempty hselected)

@[simp]
theorem restrict_rawCost (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine) :
    (restrict A selected parents hparents hselected_nonempty hselected).rawCost =
      A.rawCost := by
  cases A <;> rfl

@[simp]
theorem restrict_branchingFactor (A : AdjacentTubeStep child parent)
    (selected : Finset iota) (parents : Finset kappa)
    (hparents : ∀ p, p ∈ parents ↔
      ∃ i ∈ selected, A.parentIndex i = p)
    (hselected_nonempty : selected.Nonempty)
    (hselected : selected ⊆ A.combinatorics.index.fine) :
    (restrict A selected parents hparents hselected_nonempty hselected).combinatorics.branchingFactor =
      A.combinatorics.branchingFactor := by
  cases A with
  | partition P =>
      change (P.branchingLoss * P.branching) * 1 =
        P.branchingLoss * P.branching
      simp
  | commonFine D =>
      change (D.combinatorics.branchingLoss * D.combinatorics.branching) * 1 =
        D.combinatorics.branchingLoss * D.combinatorics.branching
      simp

end RestrictedStep.ToParentSet

/-! ## Recursive selected parent images and the rebuilt hierarchy -/

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}

/-- Starting from a selected level-zero source, retain exactly the ancestors
hit at every subsequent level.  Levels beyond the certified depth are empty. -/
def selectedLevelIndices
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (selected : Finset (Index 0)) : (l : Nat) → Finset (Index l)
  | 0 => selected
  | l + 1 =>
      if hl : l < depth then
        RestrictedStep.restrictedParents (H.step l hl)
          (selectedLevelIndices H selected l)
      else ∅

@[simp]
theorem selectedLevelIndices_zero (selected : Finset (Index 0)) :
    selectedLevelIndices H selected 0 = selected :=
  rfl

theorem selectedLevelIndices_succ (selected : Finset (Index 0))
    (l : Nat) (hl : l < depth) :
    selectedLevelIndices H selected (l + 1) =
      RestrictedStep.restrictedParents (H.step l hl)
        (selectedLevelIndices H selected l) := by
  simp [selectedLevelIndices, hl]

theorem selectedLevelIndices_nonempty
    {selected : Finset (Index 0)} (hselected : selected.Nonempty)
    (l : Nat) (hl : l ≤ depth) :
    (selectedLevelIndices H selected l).Nonempty := by
  induction l with
  | zero => simpa using hselected
  | succ l ih =>
      have hlt : l < depth := by omega
      rw [selectedLevelIndices_succ selected l hlt]
      exact RestrictedStep.restrictedParents_nonempty _ (ih (by omega))

/-- Every recursively selected ancestor remains in the original hierarchy's
certified refinement. -/
theorem selectedLevelIndices_subset_refined
    {selected : Finset (Index 0)}
    (hselected : selected ⊆ (H.family 0).refinement.refined)
    (l : Nat) (hl : l ≤ depth) :
    selectedLevelIndices H selected l ⊆
      (H.family l).refinement.refined := by
  induction l with
  | zero => simpa using hselected
  | succ l ih =>
      have hlt : l < depth := by omega
      rw [selectedLevelIndices_succ selected l hlt]
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      let A := H.step l hlt
      have hiFine : i ∈ A.combinatorics.index.fine := by
        rw [A.combinatorics.fine_eq_refined]
        exact ih (by omega) hi
      have hpCoarse := A.parentIndex_mem hiFine
      rw [A.combinatorics.coarse_eq_refined] at hpCoarse
      exact hpCoarse

abbrev SelectedHierarchyIndex
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (l : Nat) :=
  {i : Index l // i ∈ selectedLevelIndices H S.selected l}

/-- The raw level family restricted to the recursively selected subtype. -/
def selectedHierarchyFamily
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) (l : Nat) :
    UniformTubeFamily (nominalRadius l) (SelectedHierarchyIndex S l) :=
  (H.family l).restrictTo (selectedLevelIndices H S.selected l)

/-- Every selected level has the loss-one subtype refinement . -/
@[simp]
theorem selectedHierarchyFamily_refined
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) (l : Nat) :
    (selectedHierarchyFamily S l).refinement.refined = Finset.univ :=
  rfl

/-- Restrict one hierarchy step to the recursively selected children and
their exact parent image. -/
def selectedHierarchyStep
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (l : Nat) (hl : l < depth) :
    AdjacentTubeStep (selectedHierarchyFamily S l)
      (selectedHierarchyFamily S (l + 1)) := by
  have hnonempty : (selectedLevelIndices H S.selected l).Nonempty :=
    selectedLevelIndices_nonempty S.selected_nonempty l (by omega)
  have hsubset : selectedLevelIndices H S.selected l ⊆
      (H.step l hl).combinatorics.index.fine := by
    intro i hi
    rw [(H.step l hl).combinatorics.fine_eq_refined]
    exact selectedLevelIndices_subset_refined S.selected_subset_source
      l (by omega) hi
  have hparents : ∀ p,
      p ∈ selectedLevelIndices H S.selected (l + 1) ↔
        ∃ i ∈ selectedLevelIndices H S.selected l,
          (H.step l hl).parentIndex i = p := by
    intro p
    rw [selectedLevelIndices_succ S.selected l hl]
    exact Finset.mem_image
  exact RestrictedStep.ToParentSet.restrict (H.step l hl)
    (selectedLevelIndices H S.selected l)
    (selectedLevelIndices H S.selected (l + 1)) hparents
    hnonempty hsubset

/-- A complete honest hierarchy on the selected source and all of its actual
ancestor images. -/
def selectedHierarchy
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) :
    MultiscaleTubeHierarchy depth nominalRadius
      (SelectedHierarchyIndex S) where
  family := selectedHierarchyFamily S
  step := selectedHierarchyStep S

@[simp]
theorem selectedHierarchy_step_rawCost
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (l : Nat) (hl : l < depth) :
    ((selectedHierarchy S).step l hl).rawCost = (H.step l hl).rawCost := by
  change (selectedHierarchyStep S l hl).rawCost = (H.step l hl).rawCost
  unfold selectedHierarchyStep
  dsimp only
  apply RestrictedStep.ToParentSet.restrict_rawCost

@[simp]
theorem selectedHierarchy_step_branchingFactor
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (l : Nat) (hl : l < depth) :
    ((selectedHierarchy S).step l hl).combinatorics.branchingFactor =
      (H.step l hl).combinatorics.branchingFactor := by
  change (selectedHierarchyStep S l hl).combinatorics.branchingFactor =
    (H.step l hl).combinatorics.branchingFactor
  unfold selectedHierarchyStep
  dsimp only
  apply RestrictedStep.ToParentSet.restrict_branchingFactor

/-- Constructor preservation makes every accumulated geometric buffer exactly
the original buffer. -/
theorem selectedHierarchy_accumulatedBuffer_eq
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) (l : Nat) :
    (selectedHierarchy S).accumulatedBuffer l = H.accumulatedBuffer l := by
  induction l with
  | zero => rfl
  | succ l ih =>
      unfold MultiscaleTubeHierarchy.accumulatedBuffer
      by_cases hl : l < depth
      · simp only [hl, ↓reduceDIte, selectedHierarchy_step_rawCost, ih]
      · simp only [hl, ↓reduceDIte, ih]

theorem selectedHierarchy_effectiveRadius_eq
    (S : SelectedTerminalSourceChartBucketGeometry (H := H)) (l : Nat) :
    (selectedHierarchy S).effectiveRadius l = H.effectiveRadius l := by
  unfold MultiscaleTubeHierarchy.effectiveRadius
  rw [selectedHierarchy_accumulatedBuffer_eq]

/-- The selected hierarchy changes only index proofs, never tube axes. -/
theorem selectedHierarchy_effectiveFamily_axis
    (S : SelectedTerminalSourceChartBucketGeometry (H := H))
    (l : Nat) (i : SelectedHierarchyIndex S l) :
    (((selectedHierarchy S).effectiveFamily l).tubes i).axis =
      ((H.effectiveFamily l).tubes i.1).axis := by
  rfl


/-! ## Restricting the old terminal occurrence type -/

open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32ActualGraphSlopeParallelV1
open Family4GlobalExtremalUpstream
open FamilyStickyActualTubeTranslationV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1

variable {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)
  (S : SelectedTerminalSourceChartBucketGeometry (H := H))

/-- Keep every old joint path, but pair it only with a genuinely selected
level-zero source.  This avoids rebuilding or casting the path type. -/
abbrev SelectedFinalIndex :=
  C.Path × {i // i ∈ S.selected}

/-- The selected terminal occurrence is an injective subtype of the old
terminal occurrence type. -/
def selectedFinalIndexEmbedding (a : SelectedFinalIndex C S) : C.FinalIndex :=
  (a.1, ⟨a.2.1, by
    simpa only [levelZeroSource] using S.selected_subset_source a.2.2⟩)

theorem selectedFinalIndexEmbedding_injective :
    Function.Injective (selectedFinalIndexEmbedding C S) := by
  intro a b hab
  apply Prod.ext
  · simpa [selectedFinalIndexEmbedding] using congrArg Prod.fst hab
  · apply Subtype.ext
    exact congrArg (fun z : C.FinalIndex => z.2.1) hab

/-- Exact occurrence count after source restriction. -/
theorem selectedFinalIndex_card :
    Fintype.card (SelectedFinalIndex C S) =
      Fintype.card C.Path * S.selected.card := by
  classical
  rw [Fintype.card_prod, Fintype.card_coe]

/-- A definition-transparent cardinality formula for the old final index. -/
theorem finalIndex_card_eq_path_mul_source :
    Fintype.card C.FinalIndex =
      Fintype.card C.Path * (levelZeroSource (H := H)).card := by
  classical
  change Fintype.card
      (C.Path × {i // i ∈ (H.family 0).refinement.refined}) =
    Fintype.card C.Path *
      ((H.family 0).refinement.refined).card
  rw [Fintype.card_prod, Fintype.card_coe]

/-- Every source-level cardinal retention inequality propagates through all
old paths with exactly the same multiplicative loss. -/
theorem finalIndex_card_le_sourceLoss_mul_selectedFinalIndex_card
    {sourceLoss : Nat}
    (hsource : (levelZeroSource (H := H)).card ≤
      sourceLoss * S.selected.card) :
    Fintype.card C.FinalIndex ≤
      sourceLoss * Fintype.card (SelectedFinalIndex C S) := by
  rw [finalIndex_card_eq_path_mul_source C,
    selectedFinalIndex_card C S]
  calc
    Fintype.card C.Path * (levelZeroSource (H := H)).card ≤
        Fintype.card C.Path * (sourceLoss * S.selected.card) :=
      Nat.mul_le_mul_left _ hsource
    _ = sourceLoss * (Fintype.card C.Path * S.selected.card) := by
      simp only [Nat.mul_assoc, Nat.mul_comm]

/-- The actual translated terminal tube attached to a selected occurrence. -/
def selectedFinalTube (a : SelectedFinalIndex C S) :
    Tube (H.effectiveRadius 0) :=
  C.finalTube (selectedFinalIndexEmbedding C S a)

/-- Standard uniform-family interface for all selected terminal occurrences. -/
def selectedFinalTubeFamily :
    UniformTubeFamily (H.effectiveRadius 0) (SelectedFinalIndex C S) where
  tubes := selectedFinalTube C S
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem selectedFinalTubeFamily_tubes (a : SelectedFinalIndex C S) :
    (selectedFinalTubeFamily C S).tubes a = selectedFinalTube C S a :=
  rfl

@[simp]
theorem selectedFinalTubeFamily_refined :
    (selectedFinalTubeFamily C S).refinement.refined = Finset.univ :=
  rfl

/-- Selected source chart membership survives every old terminal path. -/
theorem selectedFinal_direction_two_ne_zero
    (a : SelectedFinalIndex C S) :
    ((selectedFinalTube C S a).axis.direction 2) ≠ 0 := by
  simpa [selectedFinalTube, selectedFinalIndexEmbedding,
    HierarchyJointRandomMotionCertificate.finalTube, translateTube,
    translateUnitSegment] using
      S.direction_two_ne_zero a.2.1 a.2.2

/-- The graph-c half bucket is invariant under independently chosen terminal
translations, because graph-c depends only on direction. -/
theorem selectedFinal_graphC_halfBucket
    (a b : SelectedFinalIndex C S) :
    |projectedTubeGraphC (selectedFinalTube C S a) -
      projectedTubeGraphC (selectedFinalTube C S b)| ≤
        ((H.effectiveRadius 0 : NNReal) : Real) / 2 := by
  simpa only [selectedFinalTube, selectedFinalIndexEmbedding,
    HierarchyJointRandomMotionCertificate.finalTube,
    projectedTubeGraphC_translateTube] using
      S.graphC_halfBucket a.2.1 a.2.2 b.2.1 b.2.2

/-! ## A new strong selection on the restricted terminal family -/

/-- Strong separation relation on selected terminal occurrences themselves.
Unlike the old global terminal selection, every centre necessarily lies over
`S.selected`. -/
def selectedFinalNoCommonRelation
    (a b : SelectedFinalIndex C S) : Prop :=
  NoCommonHundredContainer
    (selectedFinalTube C S a) (selectedFinalTube C S b)

theorem selectedFinalNoCommonRelation_symm :
    Std.Symm (selectedFinalNoCommonRelation C S) := by
  constructor
  intro a b hab
  exact noCommonHundredContainer_symm hab

/-- Canonical maximal strong selection rerun after source restriction. -/
def selectedTerminalStrongSelection :
    MaximalSeparatedCells (selectedFinalNoCommonRelation C S) :=
  Classical.choice
    (exists_maximalSeparatedCells (selectedFinalNoCommonRelation C S)
      (selectedFinalNoCommonRelation_symm C S))

/-- Index type of selected-source strong terminal centres. -/
abbrev SelectedTerminalStrongIndex :=
  (selectedTerminalStrongSelection C S).Cell

/-- Uniform family carried by the newly selected strong centres. -/
def selectedTerminalStrongTubeFamily :
    UniformTubeFamily (H.effectiveRadius 0)
      (SelectedTerminalStrongIndex C S) :=
  (selectedFinalTubeFamily C S).restrictTo
    (selectedTerminalStrongSelection C S).cells

@[simp]
theorem selectedTerminalStrongTubeFamily_tubes
    (a : SelectedTerminalStrongIndex C S) :
    (selectedTerminalStrongTubeFamily C S).tubes a =
      selectedFinalTube C S a.1 :=
  rfl

@[simp]
theorem selectedTerminalStrongTubeFamily_refined :
    (selectedTerminalStrongTubeFamily C S).refinement.refined = Finset.univ :=
  rfl

/-- The new centres are pairwise strongly separated. -/
theorem selectedTerminalStrongTubeFamily_pairwise_noCommon :
    Set.Pairwise (Set.univ : Set (SelectedTerminalStrongIndex C S))
      fun a b => NoCommonHundredContainer
        ((selectedTerminalStrongTubeFamily C S).tubes a)
        ((selectedTerminalStrongTubeFamily C S).tubes b) := by
  intro a _ha b _hb hab
  simpa only [selectedTerminalStrongTubeFamily_tubes,
    selectedFinalNoCommonRelation] using
      (selectedTerminalStrongSelection C S).pairwise_cell_centres
        (Set.mem_univ a) (Set.mem_univ b) hab

/-- Therefore the selected-source centres satisfy literal WZ2 essential
separation and can enter the generic coefficient machinery. -/
theorem selectedTerminalStrongTubeFamily_pairwise_wz2 :
    Set.Pairwise (Set.univ : Set (SelectedTerminalStrongIndex C S))
      fun a b => WZ2EssentiallyDistinct
        ((selectedTerminalStrongTubeFamily C S).tubes a)
        ((selectedTerminalStrongTubeFamily C S).tubes b) := by
  intro a ha b hb hab
  exact wz2EssentiallyDistinct_of_noCommonHundredContainer
    (selectedTerminalStrongTubeFamily_pairwise_noCommon C S ha hb hab)

/-- Exact finite fibre loss of the newly rerun maximal selection. -/
def selectedTerminalStrongMultiplicity : Nat :=
  Finset.univ.sup fun b : SelectedTerminalStrongIndex C S =>
    ((Finset.univ : Finset (SelectedFinalIndex C S)).filter fun a =>
      (selectedTerminalStrongSelection C S).code a = b).card

theorem selectedTerminalStrong_codeFiber_card_le
    (b : SelectedTerminalStrongIndex C S) :
    ((Finset.univ : Finset (SelectedFinalIndex C S)).filter fun a =>
      (selectedTerminalStrongSelection C S).code a = b).card ≤
        selectedTerminalStrongMultiplicity C S := by
  exact Finset.le_sup
    (s := (Finset.univ : Finset (SelectedTerminalStrongIndex C S)))
    (f := fun c =>
      ((Finset.univ : Finset (SelectedFinalIndex C S)).filter fun a =>
        (selectedTerminalStrongSelection C S).code a = c).card)
    (Finset.mem_univ b)

/-- Completely internal card loss from selected occurrences to selected
strong centres. -/
theorem selectedFinalIndex_card_le_strongMultiplicity_mul_strong_card :
    Fintype.card (SelectedFinalIndex C S) ≤
      selectedTerminalStrongMultiplicity C S *
        Fintype.card (SelectedTerminalStrongIndex C S) := by
  exact (selectedTerminalStrongSelection C S).card_le_of_fiber_bound
    (selectedTerminalStrongMultiplicity C S)
    (selectedTerminalStrong_codeFiber_card_le C S)

/-- Chart nonverticality inherited by every selected strong occurrence. -/
theorem selectedTerminalStrong_direction_two_ne_zero
    (a : SelectedTerminalStrongIndex C S) :
    ((selectedTerminalStrongTubeFamily C S).tubes a).axis.direction 2 ≠ 0 := by
  simpa only [selectedTerminalStrongTubeFamily_tubes] using
    selectedFinal_direction_two_ne_zero C S a.1

/-- Graph-c half-bucket geometry inherited by every pair of selected strong
occurrences. -/
theorem selectedTerminalStrong_graphC_halfBucket
    (a b : SelectedTerminalStrongIndex C S) :
    |projectedTubeGraphC ((selectedTerminalStrongTubeFamily C S).tubes a) -
      projectedTubeGraphC ((selectedTerminalStrongTubeFamily C S).tubes b)| ≤
        ((H.effectiveRadius 0 : NNReal) : Real) / 2 := by
  simpa only [selectedTerminalStrongTubeFamily_tubes] using
    selectedFinal_graphC_halfBucket C S a.1 b.1

/-- The exact half-coefficient parallelity premise required by the WZ2
coefficient bridge, now generated entirely from selected-source geometry. -/
theorem selectedTerminalStrong_halfCoefficient_parallel
    (j i : SelectedTerminalStrongIndex C S)
    (hi : i ∈ activeNearCoefficientIndices
      (selectedTerminalStrongTubeFamily C S) Finset.univ
      ((selectedTerminalStrongTubeFamily C S).tubes j)
      (((H.effectiveRadius 0 : NNReal) : Real) / 2)) :
    EssentiallyParallelAtScale
      ((selectedTerminalStrongTubeFamily C S).tubes i)
      ((selectedTerminalStrongTubeFamily C S).tubes j) := by
  apply essentiallyParallelAtScale_of_halfCBucket_halfCoefficient
  · exact selectedTerminalStrong_direction_two_ne_zero C S i
  · exact selectedTerminalStrong_direction_two_ne_zero C S j
  · exact selectedTerminalStrong_graphC_halfBucket C S i j
  · exact (Finset.mem_filter.mp hi).2


/-! ## Exact obstruction to casting the old joint output

The rebuilt hierarchy changes actual parent fibres.  Consequently its joint
repetition types need not be definitionally, or even cardinally, equal to the
old ones.  An embedding is enough to restrict paths, but a cast of the old
output would require coordinate equivalences plus compatibility of the
motion, tests, loads, and collision data.  These requirements are made
explicit below. -/

/-- Product path determined by one finite repetition count at each layer. -/
abbrev RepetitionPath {d : Nat} (repetitions : Fin d → Nat) :=
  ∀ k, Fin (repetitions k)

/-- Minimal data needed merely to inject newly restricted paths into old
paths.  The current hierarchy API does not manufacture these embeddings. -/
structure JointPathRestrictionCertificate {d : Nat}
    (oldRepetitions newRepetitions : Fin d → Nat) where
  coordinateEmbedding : ∀ k,
    Fin (newRepetitions k) ↪ Fin (oldRepetitions k)

namespace JointPathRestrictionCertificate

/-- Coordinate embeddings induce the strongest automatic path-level
restriction map one can expect without equality of repetition counts. -/
def pathEmbedding {d : Nat}
    {oldRepetitions newRepetitions : Fin d → Nat}
    (T : JointPathRestrictionCertificate oldRepetitions newRepetitions) :
    RepetitionPath newRepetitions ↪ RepetitionPath oldRepetitions where
  toFun := fun p k => T.coordinateEmbedding k (p k)
  inj' := by
    intro p q hpq
    funext k
    exact (T.coordinateEmbedding k).injective (congrFun hpq k)

end JointPathRestrictionCertificate

/-- Concrete semantic fields additionally needed to transport an old joint
output along a path restriction.  The types record, rather than assume, the
missing omega compatibility, active-test inclusion, and load/collision
control. -/
structure JointOutputRestrictionTransportCertificate
    {d : Nat} {test : Type v} [DecidableEq test]
    (oldRepetitions newRepetitions : Fin d → Nat)
    (oldOmega : RepetitionPath oldRepetitions → Space)
    (newOmega : RepetitionPath newRepetitions → Space)
    (oldActiveTests : RepetitionPath oldRepetitions → Finset test)
    (newActiveTests : RepetitionPath newRepetitions → Finset test)
    (oldLoad oldCollision : RepetitionPath oldRepetitions → Nat)
    (newLoad newCollision : RepetitionPath newRepetitions → Nat) where
  path : JointPathRestrictionCertificate oldRepetitions newRepetitions
  omega_compatible : ∀ p,
    newOmega p = oldOmega (path.pathEmbedding p)
  activeTests_subset : ∀ p,
    newActiveTests p ⊆ oldActiveTests (path.pathEmbedding p)
  load_le : ∀ p, newLoad p ≤ oldLoad (path.pathEmbedding p)
  collision_le : ∀ p,
    newCollision p ≤ oldCollision (path.pathEmbedding p)

/-- A literal cast, unlike a restriction embedding, requires an equivalence
at every repetition coordinate. -/
structure JointPathCastCertificate {d : Nat}
    (oldRepetitions newRepetitions : Fin d → Nat) where
  coordinateEquiv : ∀ k,
    Fin (newRepetitions k) ≃ Fin (oldRepetitions k)

namespace JointPathCastCertificate

/-- Coordinate equivalence forces equality of every repetition count. -/
theorem repetitions_eq {d : Nat}
    {oldRepetitions newRepetitions : Fin d → Nat}
    (T : JointPathCastCertificate oldRepetitions newRepetitions)
    (k : Fin d) :
    newRepetitions k = oldRepetitions k := by
  simpa using Fintype.card_congr (T.coordinateEquiv k)

end JointPathCastCertificate

/-- One selected repetition can honestly embed into two old repetitions. -/
def oneRepetition : Fin 1 → Nat := fun _ => 1

def twoRepetitions : Fin 1 → Nat := fun _ => 2

/-- Sharp one-layer restriction witness: the new path coordinate injects into
the old coordinate, so restriction is possible. -/
def oneIntoTwoPathRestriction :
    JointPathRestrictionCertificate twoRepetitions oneRepetition where
  coordinateEmbedding := fun _ =>
    ⟨fun _ => (0 : Fin 2), fun a b _ => by
      change Fin 1 at a b
      exact Subsingleton.elim a b⟩

/-- But no path cast certificate can exist in the same finite example.  Thus
old and rebuilt joint outputs cannot be cast from hierarchy data alone. -/
theorem no_oneIntoTwoPathCast :
    ¬ Nonempty (JointPathCastCertificate twoRepetitions oneRepetition) := by
  rintro ⟨T⟩
  have h := T.repetitions_eq (0 : Fin 1)
  norm_num [oneRepetition, twoRepetitions] at h

/-! ## Direct consumption by the generic coefficient bridge -/

open FamilyStickyWZ2SameScaleCoefficientCapV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1

/-- Same-radius cover interface for the selected-source strong family. -/
abbrev SelectedTerminalStrongSameScaleCover :=
  @TubeScaleCover (H.effectiveRadius 0) (H.effectiveRadius 0)
    (SelectedTerminalStrongIndex C S) _
    (selectedTerminalStrongTubeFamily C S) Finset.univ

/-- A canonical cover exists without any additional hierarchy output. -/
noncomputable def selectedTerminalStrongIdentityCover :
    SelectedTerminalStrongSameScaleCover C S :=
  identityUnivTubeScaleCover (selectedTerminalStrongTubeFamily C S)

@[simp]
theorem selectedTerminalStrongIdentityCover_count :
    (selectedTerminalStrongIdentityCover C S).count =
      Fintype.card (SelectedTerminalStrongIndex C S) :=
  rfl

/-- Pairwise WZ2 separation restricted to the literal active finset expected
by the generic coefficient API. -/
theorem selectedTerminalStrongTubeFamily_pairwise_wz2_on_activeUniv :
    Set.Pairwise
      ((Finset.univ : Finset (SelectedTerminalStrongIndex C S)) :
        Set (SelectedTerminalStrongIndex C S))
      fun a b => WZ2EssentiallyDistinct
        ((selectedTerminalStrongTubeFamily C S).tubes a)
        ((selectedTerminalStrongTubeFamily C S).tubes b) := by
  intro a _ha b _hb hab
  exact selectedTerminalStrongTubeFamily_pairwise_wz2 C S
    (Set.mem_univ a) (Set.mem_univ b) hab

/-- Full-radius coefficient-fibre cap for the selected-source strong family.
There is no whole-source geometry assumption in this endpoint. -/
theorem selectedTerminalStrong_activeNearCoefficientIndices_card_le_fullCap
    (Q : SelectedTerminalStrongSameScaleCover C S)
    (hdelta : 0 < H.effectiveRadius 0)
    (center : Tube (H.effectiveRadius 0)) :
    (activeNearCoefficientIndices (selectedTerminalStrongTubeFamily C S)
      Finset.univ center ((H.effectiveRadius 0 : NNReal) : Real)).card ≤
      actualHalfScaleCoefficientCoverLoss * Q.count := by
  apply activeNearCoefficientIndices_card_le_coverLoss_mul_count_wz2
    Q hdelta
      (selectedTerminalStrongTubeFamily_pairwise_wz2_on_activeUniv C S)
  intro j _hj i hi
  exact selectedTerminalStrong_halfCoefficient_parallel C S j i hi

/-- The selected strong cardinal is retained by concrete coefficient centres
with the explicit same-scale cover multiplicity. -/
theorem selectedTerminalStrong_card_le_fullCap_mul_selectedTubes_card
    (Q : SelectedTerminalStrongSameScaleCover C S)
    (hdelta : 0 < H.effectiveRadius 0) :
    Fintype.card (SelectedTerminalStrongIndex C S) ≤
      (actualHalfScaleCoefficientCoverLoss * Q.count) *
        (selectedTubes
          (activeTubeImage (selectedTerminalStrongTubeFamily C S) Finset.univ)
          ((H.effectiveRadius 0 : NNReal) : Real)).card := by
  have hscale : 0 < ((H.effectiveRadius 0 : NNReal) : Real) := by
    exact_mod_cast hdelta
  have hcap : ∀ center,
      center ∈ selectedTubes
        (activeTubeImage (selectedTerminalStrongTubeFamily C S) Finset.univ)
        ((H.effectiveRadius 0 : NNReal) : Real) →
      (activeNearCoefficientIndices (selectedTerminalStrongTubeFamily C S)
        Finset.univ center ((H.effectiveRadius 0 : NNReal) : Real)).card ≤
          actualHalfScaleCoefficientCoverLoss * Q.count := by
    intro center _hcenter
    exact selectedTerminalStrong_activeNearCoefficientIndices_card_le_fullCap
      C S Q hdelta center
  simpa only [Finset.card_univ] using
    (active_card_le_multiplicity_mul_selectedTubes_card_of_pairwise_wz2
      (selectedTerminalStrongTubeFamily_pairwise_wz2_on_activeUniv C S)
      hscale (actualHalfScaleCoefficientCoverLoss * Q.count) hcap)

/-- End-to-end cardinal bridge: an honest source bucket loss propagates over
all old paths, through a freshly rerun strong selection, and into the generic
coefficient-selected family. -/
theorem finalIndex_card_le_sourceLoss_mul_strongMultiplicity_mul_coefficient_card
    {sourceLoss : Nat}
    (hsource : (levelZeroSource (H := H)).card ≤
      sourceLoss * S.selected.card)
    (Q : SelectedTerminalStrongSameScaleCover C S)
    (hdelta : 0 < H.effectiveRadius 0) :
    Fintype.card C.FinalIndex ≤
      sourceLoss *
        (selectedTerminalStrongMultiplicity C S *
          ((actualHalfScaleCoefficientCoverLoss * Q.count) *
            (selectedTubes
              (activeTubeImage (selectedTerminalStrongTubeFamily C S)
                Finset.univ)
              ((H.effectiveRadius 0 : NNReal) : Real)).card)) := by
  calc
    Fintype.card C.FinalIndex ≤
        sourceLoss * Fintype.card (SelectedFinalIndex C S) :=
      finalIndex_card_le_sourceLoss_mul_selectedFinalIndex_card C S hsource
    _ ≤ sourceLoss *
        (selectedTerminalStrongMultiplicity C S *
          Fintype.card (SelectedTerminalStrongIndex C S)) :=
      Nat.mul_le_mul_left sourceLoss
        (selectedFinalIndex_card_le_strongMultiplicity_mul_strong_card C S)
    _ ≤ sourceLoss *
        (selectedTerminalStrongMultiplicity C S *
          ((actualHalfScaleCoefficientCoverLoss * Q.count) *
            (selectedTubes
              (activeTubeImage (selectedTerminalStrongTubeFamily C S)
                Finset.univ)
              ((H.effectiveRadius 0 : NNReal) : Real)).card)) :=
      Nat.mul_le_mul_left sourceLoss
        (Nat.mul_le_mul_left (selectedTerminalStrongMultiplicity C S)
          (selectedTerminalStrong_card_le_fullCap_mul_selectedTubes_card
            C S Q hdelta))
#print axioms selectedHierarchy_effectiveRadius_eq
#print axioms finalIndex_card_le_sourceLoss_mul_strongMultiplicity_mul_coefficient_card
#print axioms no_oneIntoTwoPathCast

end

end FamilyStickyHierarchySelectedSourceNestedRestrictionV1
