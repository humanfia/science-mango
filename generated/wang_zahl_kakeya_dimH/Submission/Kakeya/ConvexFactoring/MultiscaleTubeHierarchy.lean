import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Submission.Kakeya.ConvexFactoring.TubeCommonSegment

open Set
open scoped NNReal

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# Honest buffered multiscale tube hierarchies

The raw families below retain their nominal radii.  Every adjacent step is
either an already certified `CoarseTubePartition`, or combinatorial partition
data together with a common-fine-tube witness for each active child.  A step
has an explicit geometric cost: zero in the first case and four times the
child's nominal radius in the second case.

Accumulated buffers are the sums of these costs.  Thus the effective radius at
level `l` is exactly `nominalRadius l + accumulatedBuffer l`; it is never
identified with the nominal radius.  An upper comparison with the nominal
radius is exposed only after a separate comparison certificate is supplied.

This module assembles a multiscale hierarchy from supplied adjacent-step data.
It does not assert that the required partitions or common-fine covers exist
for an arbitrary family of tubes or from the Wang--Zahl hypotheses alone.
-/

/-- The non-geometric fields of a coarse tube partition. -/
structure TubePartitionCombinatorics
    {r R : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (child : UniformTubeFamily r ι) (parent : UniformTubeFamily R κ) where
  scale_le : r ≤ R
  index : IndexFactorization ι κ
  fine_eq_refined : index.fine = child.refinement.refined
  coarse_eq_refined : index.coarse = parent.refinement.refined
  coarse_nonempty : index.coarse.Nonempty
  parent_surjective : ∀ k ∈ index.coarse,
    ∃ i ∈ index.fine, index.parent i = k
  branching : ℕ
  branching_pos : 0 < branching
  branchingLoss : ℕ
  branchingLoss_pos : 0 < branchingLoss
  branching_le_loss_mul_fiber : ∀ k ∈ index.coarse,
    branching ≤ branchingLoss * (index.fiber k).card
  fiber_card_le_loss_mul_branching : ∀ k ∈ index.coarse,
    (index.fiber k).card ≤ branchingLoss * branching

namespace TubePartitionCombinatorics

/-- Forget only the geometric containment field of an actual partition. -/
def ofPartition
    {r R : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {child : UniformTubeFamily r ι} {parent : UniformTubeFamily R κ}
    (P : CoarseTubePartition child parent) :
    TubePartitionCombinatorics child parent where
  scale_le := P.scale_le
  index := P.index
  fine_eq_refined := P.fine_eq_refined
  coarse_eq_refined := P.coarse_eq_refined
  coarse_nonempty := P.coarse_nonempty
  parent_surjective := P.parent_surjective
  branching := P.branching
  branching_pos := P.branching_pos
  branchingLoss := P.branchingLoss
  branchingLoss_pos := P.branchingLoss_pos
  branching_le_loss_mul_fiber := P.branching_le_loss_mul_fiber
  fiber_card_le_loss_mul_branching := P.fiber_card_le_loss_mul_branching

/-- One-step upper branching factor, including the certified loss. -/
def branchingFactor
    {r R : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {child : UniformTubeFamily r ι} {parent : UniformTubeFamily R κ}
    (C : TubePartitionCombinatorics child parent) : ℕ :=
  C.branchingLoss * C.branching

/-- The active child cardinality is bounded by the active parent cardinality
times the one-step branching factor. -/
theorem activeCard_le
    {r R : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {child : UniformTubeFamily r ι} {parent : UniformTubeFamily R κ}
    (C : TubePartitionCombinatorics child parent) :
    child.refinement.refined.card ≤
      parent.refinement.refined.card * C.branchingFactor := by
  rw [← C.fine_eq_refined, C.index.card_eq_sum_card_fiber]
  calc
    (∑ k ∈ C.index.coarse, (C.index.fiber k).card) ≤
        ∑ _k ∈ C.index.coarse, C.branchingFactor :=
      Finset.sum_le_sum fun k hk ↦ C.fiber_card_le_loss_mul_branching k hk
    _ = C.index.coarse.card * C.branchingFactor := by simp
    _ = parent.refinement.refined.card * C.branchingFactor := by
      rw [C.coarse_eq_refined]

end TubePartitionCombinatorics

/-- A common-fine-tube realization of the geometric field missing from
`TubePartitionCombinatorics`.  The witness radius may depend on the child. -/
structure CommonFineTubeCoverData
    {r R : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (child : UniformTubeFamily r ι) (parent : UniformTubeFamily R κ) where
  combinatorics : TubePartitionCombinatorics child parent
  commonFine : ∀ i ∈ combinatorics.index.fine,
    ∃ δ : NNReal, ∃ fine : Tube δ,
      fine.carrier ⊆ (child.tubes i).carrier ∧
      fine.carrier ⊆ (parent.tubes (combinatorics.index.parent i)).carrier

/-- An adjacent raw step is justified either by an actual exact partition or
by common-fine-tube cover data. -/
inductive AdjacentTubeStep
    {r R : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (child : UniformTubeFamily r ι) (parent : UniformTubeFamily R κ) where
  | partition (P : CoarseTubePartition child parent)
  | commonFine (D : CommonFineTubeCoverData child parent)

namespace AdjacentTubeStep

variable {r R : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {child : UniformTubeFamily r ι} {parent : UniformTubeFamily R κ}

/-- Combinatorial data shared by both kinds of adjacent step. -/
def combinatorics (S : AdjacentTubeStep child parent) :
    TubePartitionCombinatorics child parent :=
  match S with
  | .partition P => TubePartitionCombinatorics.ofPartition P
  | .commonFine D => D.combinatorics

/-- Raw geometric cost that the parent buffer must absorb. -/
def rawCost (S : AdjacentTubeStep child parent) : NNReal :=
  match S with
  | .partition _ => 0
  | .commonFine _ => 4 * r

/-- Parent index selected at this step. -/
def parentIndex (S : AdjacentTubeStep child parent) (i : ι) : κ :=
  S.combinatorics.index.parent i

/-- Active indices map to active parent indices. -/
theorem parentIndex_mem (S : AdjacentTubeStep child parent)
    {i : ι} (hi : i ∈ S.combinatorics.index.fine) :
    S.parentIndex i ∈ S.combinatorics.index.coarse :=
  S.combinatorics.index.parent_mem i hi

/-- Every active child is contained in the closed neighborhood of its raw
parent having exactly the declared geometric cost. -/
theorem raw_carrier_subset (S : AdjacentTubeStep child parent)
    (i : ι) (hi : i ∈ S.combinatorics.index.fine) :
    (child.tubes i).carrier ⊆
      Metric.cthickening (S.rawCost : ℝ)
        (parent.tubes (S.parentIndex i)).carrier := by
  cases S with
  | partition P =>
      exact (P.carrier_subset i hi).trans
        (Metric.self_subset_cthickening _)
  | commonFine D =>
      obtain ⟨δ, fine, hFineChild, hFineParent⟩ := D.commonFine i hi
      simpa [rawCost, parentIndex, combinatorics, NNReal.coe_mul] using
        Tube.carrier_subset_four_mul_cthickening_of_commonFineTube
          fine (child.tubes i) (parent.tubes (D.combinatorics.index.parent i))
          hFineChild hFineParent

/-- Recursive buffer absorption for either kind of step. -/
theorem buffered_carrier_subset (S : AdjacentTubeStep child parent)
    (q : NNReal) (i : ι) (hi : i ∈ S.combinatorics.index.fine) :
    ((child.tubes i).buffer q).carrier ⊆
      ((parent.tubes (S.parentIndex i)).buffer (S.rawCost + q)).carrier :=
  Tube.buffer_subset_buffer_add_of_subset_cthickening
    (S.raw_carrier_subset i hi)

end AdjacentTubeStep

/-- A finite raw hierarchy.  Data are Nat-indexed to make genuinely dependent
parent composition transparent; only levels `0, ..., depth` are part of the
certified hierarchy. -/
structure MultiscaleTubeHierarchy
    (depth : Nat) (nominalRadius : Nat → NNReal)
    (Index : Nat → Type*) [∀ l, DecidableEq (Index l)] where
  family : (l : Nat) → UniformTubeFamily (nominalRadius l) (Index l)
  step : ∀ l, l < depth → AdjacentTubeStep (family l) (family (l + 1))

namespace MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*} [∀ l, DecidableEq (Index l)]

/-- Sum of all raw geometric costs strictly below a level. -/
def accumulatedBuffer
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Nat → NNReal
  | 0 => 0
  | l + 1 =>
      if hl : l < depth then
        (H.step l hl).rawCost + H.accumulatedBuffer l
      else
        H.accumulatedBuffer l

@[simp] theorem accumulatedBuffer_zero
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) :
    H.accumulatedBuffer 0 = 0 :=
  rfl

theorem accumulatedBuffer_succ
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (hl : l < depth) :
    H.accumulatedBuffer (l + 1) =
      (H.step l hl).rawCost + H.accumulatedBuffer l := by
  simp [accumulatedBuffer, hl]

/-- The certified radius after recursive buffering. -/
def effectiveRadius
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) (l : Nat) : NNReal :=
  nominalRadius l + H.accumulatedBuffer l

/-- The actual family used by the buffered hierarchy. -/
def effectiveFamily
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) (l : Nat) :
    UniformTubeFamily (H.effectiveRadius l) (Index l) :=
  (H.family l).buffer (H.accumulatedBuffer l)

@[simp] theorem effectiveFamily_tubes
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (i : Index l) :
    (H.effectiveFamily l).tubes i =
      ((H.family l).tubes i).buffer (H.accumulatedBuffer l) :=
  rfl

/-- Nominal radii are always lower bounds for effective radii. -/
theorem nominalRadius_le_effectiveRadius
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) (l : Nat) :
    nominalRadius l ≤ H.effectiveRadius l := by
  exact le_add_right le_rfl

/-- Effective radii are nondecreasing across certified adjacent steps. -/
theorem effectiveRadius_step_le
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (hl : l < depth) :
    H.effectiveRadius l ≤ H.effectiveRadius (l + 1) := by
  rw [effectiveRadius, effectiveRadius, H.accumulatedBuffer_succ l hl]
  exact add_le_add (H.step l hl).combinatorics.scale_le (le_add_left le_rfl)

/-- Exact carrier containment at one recursively buffered step. -/
theorem effective_carrier_subset_parent
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (hl : l < depth) (i : Index l)
    (hi : i ∈ (H.family l).refinement.refined) :
    ((H.effectiveFamily l).tubes i).carrier ⊆
      ((H.effectiveFamily (l + 1)).tubes
        ((H.step l hl).parentIndex i)).carrier := by
  have hi' : i ∈ (H.step l hl).combinatorics.index.fine := by
    rw [(H.step l hl).combinatorics.fine_eq_refined]
    exact hi
  change (((H.family l).tubes i).buffer (H.accumulatedBuffer l)).carrier ⊆
    (((H.family (l + 1)).tubes ((H.step l hl).parentIndex i)).buffer
      (H.accumulatedBuffer (l + 1))).carrier
  rw [H.accumulatedBuffer_succ l hl]
  exact (H.step l hl).buffered_carrier_subset
    (H.accumulatedBuffer l) i hi'

/-- Recursive buffering turns every raw step into an actual coarse partition
between families indexed by their effective radii. -/
def effectivePartition
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (hl : l < depth) :
    CoarseTubePartition (H.effectiveFamily l) (H.effectiveFamily (l + 1)) := by
  let S := H.step l hl
  let C := S.combinatorics
  refine
    { scale_le := H.effectiveRadius_step_le l hl
      index := C.index
      fine_eq_refined := ?_
      coarse_eq_refined := ?_
      coarse_nonempty := C.coarse_nonempty
      carrier_subset := ?_
      parent_surjective := C.parent_surjective
      branching := C.branching
      branching_pos := C.branching_pos
      branchingLoss := C.branchingLoss
      branchingLoss_pos := C.branchingLoss_pos
      branching_le_loss_mul_fiber := C.branching_le_loss_mul_fiber
      fiber_card_le_loss_mul_branching := C.fiber_card_le_loss_mul_branching }
  · simpa [C, S, effectiveFamily, UniformTubeFamily.buffer] using
      C.fine_eq_refined
  · simpa [C, S, effectiveFamily, UniformTubeFamily.buffer] using
      C.coarse_eq_refined
  · intro i hi
    have hi' : i ∈ (H.family l).refinement.refined := by
      rw [← C.fine_eq_refined]
      exact hi
    exact H.effective_carrier_subset_parent l hl i
      (by simpa [C, S] using hi')

/-- Transporting a dependent index along an equality of levels preserves
active membership. -/
theorem mem_transport
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    {a b : Nat} (hab : a = b) {i : Index a}
    (hi : i ∈ (H.family a).refinement.refined) :
    (hab ▸ i) ∈ (H.family b).refinement.refined := by
  subst b
  exact hi

/-- Composed parent index after `steps` successive levels. -/
def ancestor
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) (start : Nat) :
    (steps : Nat) → start + steps ≤ depth → Index start → Index (start + steps)
  | 0, _, i => i
  | steps + 1, h, i =>
      (H.step (start + steps) (by omega)).parentIndex
        (H.ancestor start steps (by omega) i)

@[simp] theorem ancestor_zero
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (start : Nat) (h : start ≤ depth) (i : Index start) :
    H.ancestor start 0 (by simpa using h) i = i :=
  rfl

theorem ancestor_succ
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (start steps : Nat) (h : start + (steps + 1) ≤ depth) (i : Index start) :
    H.ancestor start (steps + 1) h i =
      (H.step (start + steps) (by omega)).parentIndex
        (H.ancestor start steps (by omega) i) :=
  rfl

/-- Parent composition preserves active-index membership along the path. -/
theorem ancestor_mem
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (start steps : Nat) (h : start + steps ≤ depth) (i : Index start)
    (hi : i ∈ (H.family start).refinement.refined) :
    H.ancestor start steps h i ∈
      (H.family (start + steps)).refinement.refined := by
  induction steps with
  | zero => simpa [ancestor] using hi
  | succ steps ih =>
      have hprev : start + steps ≤ depth := by omega
      have hlevel : start + steps < depth := by omega
      let S := H.step (start + steps) hlevel
      have hmid := ih hprev
      have hmid' : H.ancestor start steps hprev i ∈
          S.combinatorics.index.fine := by
        rw [S.combinatorics.fine_eq_refined]
        simpa [S] using hmid
      have hp := S.parentIndex_mem hmid'
      rw [S.combinatorics.coarse_eq_refined] at hp
      have hadd : start + steps + 1 = start + (steps + 1) := by omega
      have hp' := H.mem_transport hadd hp
      simpa only [ancestor, S] using hp'

/-- Exact nested carrier containment along an arbitrary parent path. -/
theorem effective_carrier_subset_ancestor
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (start steps : Nat) (h : start + steps ≤ depth) (i : Index start)
    (hi : i ∈ (H.family start).refinement.refined) :
    ((H.effectiveFamily start).tubes i).carrier ⊆
      ((H.effectiveFamily (start + steps)).tubes
        (H.ancestor start steps h i)).carrier := by
  induction steps with
  | zero => simp [ancestor]
  | succ steps ih =>
      have hprev : start + steps ≤ depth := by omega
      have hlevel : start + steps < depth := by omega
      exact (ih hprev).trans
        (H.effective_carrier_subset_parent (start + steps) hlevel
          (H.ancestor start steps hprev i)
          (H.ancestor_mem start steps hprev i hi))

/-- Product of the upper branching factors along a path. -/
def branchingProduct
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) (start : Nat) :
    (steps : Nat) → start + steps ≤ depth → Nat
  | 0, _ => 1
  | steps + 1, h =>
      (H.step (start + steps) (by omega)).combinatorics.branchingFactor *
        H.branchingProduct start steps (by omega)

@[simp] theorem branchingProduct_zero
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (start : Nat) (h : start ≤ depth) :
    H.branchingProduct start 0 (by simpa using h) = 1 :=
  rfl

theorem branchingProduct_succ
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (start steps : Nat) (h : start + (steps + 1) ≤ depth) :
    H.branchingProduct start (steps + 1) h =
      (H.step (start + steps) (by omega)).combinatorics.branchingFactor *
        H.branchingProduct start steps (by omega) :=
  rfl

/-- Iterating the one-step fiber bounds gives the honest branching-product
bound between the active cardinalities at the endpoints of a path. -/
theorem activeCard_le_mul_branchingProduct
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (start steps : Nat) (h : start + steps ≤ depth) :
    (H.family start).refinement.refined.card ≤
      (H.family (start + steps)).refinement.refined.card *
        H.branchingProduct start steps h := by
  induction steps with
  | zero => simp [branchingProduct]
  | succ steps ih =>
      have hprev : start + steps ≤ depth := by omega
      have hlevel : start + steps < depth := by omega
      let C := (H.step (start + steps) hlevel).combinatorics
      have hstep := C.activeCard_le
      have hadd : start + steps + 1 = start + (steps + 1) := by omega
      calc
        (H.family start).refinement.refined.card ≤
            (H.family (start + steps)).refinement.refined.card *
              H.branchingProduct start steps hprev := ih hprev
        _ ≤ ((H.family (start + steps + 1)).refinement.refined.card *
              C.branchingFactor) *
              H.branchingProduct start steps hprev :=
            Nat.mul_le_mul_right _ hstep
        _ = (H.family (start + (steps + 1))).refinement.refined.card *
              H.branchingProduct start (steps + 1) h := by
            rw [H.branchingProduct_succ start steps h, ← hadd]
            simp only [C, Nat.mul_assoc]

/-- Additional data needed for any upper comparison between effective and
nominal radii.  Such a comparison is not derivable from the hierarchy alone. -/
structure NominalComparison
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) where
  factor : NNReal
  buffer_le : ∀ l, l ≤ depth →
    H.accumulatedBuffer l ≤ factor * nominalRadius l

namespace NominalComparison

/-- A supplied buffer comparison gives a multiplicative effective-radius
comparison; the hierarchy itself only gives the opposite inequality. -/
theorem effectiveRadius_le
    {H : MultiscaleTubeHierarchy depth nominalRadius Index}
    (C : H.NominalComparison) (l : Nat) (hl : l ≤ depth) :
    H.effectiveRadius l ≤ (1 + C.factor) * nominalRadius l := by
  calc
    H.effectiveRadius l = nominalRadius l + H.accumulatedBuffer l := rfl
    _ ≤ nominalRadius l + C.factor * nominalRadius l :=
      add_le_add le_rfl (C.buffer_le l hl)
    _ = (1 + C.factor) * nominalRadius l := by ring

end NominalComparison

end MultiscaleTubeHierarchy

end

end Submission.Kakeya.ConvexFactoring
