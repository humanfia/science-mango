import Family4GlobalExtremalUpstream
import Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set
open scoped ENNReal NNReal

namespace Family8GreedySuppliedCoverJointStickyScaleCoverV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Jointly refining greedy occurrences by a supplied tube cover

A greedy occurrence partition and a supplied `TubeScaleCover` need not use
the same parent classes.  Their honest common refinement labels an active
fine index by the pair

`(its greedy occurrence, its supplied tube parent)`.

Only occupied pairs are retained and then canonically enumerated by `Fin`.
The geometric parent tube is the supplied parent's actual radius-`tau` tube,
so carrier containment is inherited without any normalized-axis pullback.

This construction splits a greedy block along supplied-cover fibers.  It
therefore does **not** assert that a joint fiber inherits the whole block's
maximal-density or Frostman conclusion.  Such inheritance requires a
separate compatibility theorem (or a new greedy construction inside each
supplied fiber).
-/

universe u v

variable {delta tau : NNReal}
  {iota : Type u} {kappa : Type v}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}
  {candidates : Finset kappa}
  {container : kappa → ConvexBody Space}

/-- The literal active fine subtype used by the joint cover. -/
abbrev JointActiveFine := {i // i ∈ active}

/-- Pair of an actual greedy occurrence and a supplied coarse code. -/
abbrev JointParentCode
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :=
  Fin (blocks fine.bodyFamily P).length × Fin C.count

/-- The two genuine parent labels attached to one active fine index. -/
def jointCode
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : JointActiveFine (active := active)) : JointParentCode P C :=
  (locate fine.bodyFamily P i.2, C.parent i.1)

/-- Exactly the greedy/supplied pairs hit by active fine indices. -/
def occupiedJointParents
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    Finset (JointParentCode P C) :=
  (Finset.univ : Finset (JointActiveFine (active := active))).image
    (jointCode P C)

@[simp]
theorem mem_occupiedJointParents
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (z : JointParentCode P C) :
    z ∈ occupiedJointParents P C ↔
      ∃ i : JointActiveFine (active := active), jointCode P C i = z := by
  simp [occupiedJointParents]

/-- Canonical enumeration of only the occupied joint codes. -/
def occupiedJointParentEquiv
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    {z // z ∈ occupiedJointParents P C} ≃
      Fin (occupiedJointParents P C).card :=
  (occupiedJointParents P C).equivFin

/-- The occurrence/supplied joint refinement as a genuine sticky scale
cover.  Repeated supplied tubes in different greedy blocks remain distinct
coarse occurrences, while unused pairs are absent. -/
def greedySuppliedJointStickyScaleCover
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    StickyScaleCover (fine.restrictTo active) tau := by
  classical
  let e := occupiedJointParentEquiv P C
  let coarse : UniformTubeFamily tau (Fin (occupiedJointParents P C).card) :=
    { tubes := fun q ↦ C.tubes (e.symm q).1.2
      refinement := UniformRefinement.ofFinset Finset.univ }
  exact
    { coarseCard := (occupiedJointParents P C).card
      coarse := coarse
      activeFine := Finset.univ
      activeCoarse := Finset.univ
      parent := fun i ↦ e ⟨jointCode P C i, by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
      activeFine_eq_refined := rfl
      activeCoarse_eq_refined := rfl
      parent_mem := by simp
      parent_surjective := by
        intro q _hq
        let z : {z // z ∈ occupiedJointParents P C} := e.symm q
        obtain ⟨i, _hi, hiz⟩ := Finset.mem_image.mp z.2
        refine ⟨i, Finset.mem_univ i, ?_⟩
        change e ⟨jointCode P C i, by
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ = q
        have heq :
            (⟨jointCode P C i, by
              exact Finset.mem_image.mpr
                ⟨i, Finset.mem_univ i, rfl⟩⟩ :
              {z // z ∈ occupiedJointParents P C}) = z := by
          apply Subtype.ext
          exact hiz
        rw [heq, e.apply_symm_apply]
      carrier_subset := by
        intro i _hi
        have hsource := C.carrier_subset i.1 i.2
        change (fine.tubes i.1).carrier ⊆
          (C.tubes
            (e.symm (e ⟨jointCode P C i, by
              exact Finset.mem_image.mpr
                ⟨i, Finset.mem_univ i, rfl⟩⟩)).1.2).carrier
        rw [e.symm_apply_apply]
        exact hsource }

@[simp]
theorem greedySuppliedJointStickyScaleCover_coarseCard
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (greedySuppliedJointStickyScaleCover P C).coarseCard =
      (occupiedJointParents P C).card :=
  rfl

@[simp]
theorem greedySuppliedJointStickyScaleCover_activeFine
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (greedySuppliedJointStickyScaleCover P C).activeFine = Finset.univ :=
  rfl

@[simp]
theorem greedySuppliedJointStickyScaleCover_activeCoarse
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (greedySuppliedJointStickyScaleCover P C).activeCoarse = Finset.univ :=
  rfl

/-- Decoding the canonical parent recovers the exact joint code assigned to
the fine index. -/
theorem parent_decodes_jointCode
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : JointActiveFine (active := active)) :
    (occupiedJointParentEquiv P C).symm
        ((greedySuppliedJointStickyScaleCover P C).parent i) =
      ⟨jointCode P C i, by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ := by
  exact (occupiedJointParentEquiv P C).symm_apply_apply _

/-- The first decoded coordinate is the genuine greedy occurrence. -/
theorem parent_decodes_greedyOccurrence
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : JointActiveFine (active := active)) :
    ((occupiedJointParentEquiv P C).symm
      ((greedySuppliedJointStickyScaleCover P C).parent i)).1.1 =
        locate fine.bodyFamily P i.2 := by
  have h := congrArg (fun z => z.1.1) (parent_decodes_jointCode P C i)
  exact h

/-- The second decoded coordinate is the genuine supplied tube parent. -/
theorem parent_decodes_suppliedParent
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : JointActiveFine (active := active)) :
    ((occupiedJointParentEquiv P C).symm
      ((greedySuppliedJointStickyScaleCover P C).parent i)).1.2 =
        C.parent i.1 := by
  have h := congrArg (fun z => z.1.2) (parent_decodes_jointCode P C i)
  exact h

/-- Every fine index belongs to the greedy block recorded by its decoded
joint parent. -/
theorem fine_mem_decoded_greedyBlock
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : JointActiveFine (active := active)) :
    i.1 ∈
      (blockAt fine.bodyFamily P
        ((occupiedJointParentEquiv P C).symm
          ((greedySuppliedJointStickyScaleCover P C).parent i)).1.1).fiber := by
  rw [parent_decodes_greedyOccurrence P C i]
  exact mem_blockAt_locate fine.bodyFamily P i.2

/-- The concrete coarse tube of a joint parent is exactly its decoded
supplied tube; no normalized proxy is inserted. -/
theorem coarse_tube_eq_decoded_suppliedTube
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (q : Fin (occupiedJointParents P C).card) :
    (greedySuppliedJointStickyScaleCover P C).coarse.tubes q =
      C.tubes ((occupiedJointParentEquiv P C).symm q).1.2 :=
  rfl

/-- At the parent of `i`, the concrete coarse tube is precisely `C.parent
i`, so the original supplied carrier containment is recovered literally. -/
theorem parent_tube_eq_suppliedParentTube
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : JointActiveFine (active := active)) :
    (greedySuppliedJointStickyScaleCover P C).coarse.tubes
        ((greedySuppliedJointStickyScaleCover P C).parent i) =
      C.tubes (C.parent i.1) := by
  change C.tubes
      ((occupiedJointParentEquiv P C).symm
        ((greedySuppliedJointStickyScaleCover P C).parent i)).1.2 =
    C.tubes (C.parent i.1)
  rw [parent_decodes_suppliedParent P C i]

theorem fine_carrier_subset_joint_parent
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : JointActiveFine (active := active)) :
    (fine.tubes i.1).carrier ⊆
      ((greedySuppliedJointStickyScaleCover P C).coarse.tubes
        ((greedySuppliedJointStickyScaleCover P C).parent i)).carrier := by
  rw [parent_tube_eq_suppliedParentTube P C i]
  exact C.carrier_subset i.1 i.2

/-! ## Exact finite cardinality bounds -/

theorem occupiedJointParents_card_le_active
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (occupiedJointParents P C).card ≤ active.card := by
  calc
    (occupiedJointParents P C).card ≤
        (Finset.univ : Finset (JointActiveFine (active := active))).card :=
      Finset.card_image_le
    _ = active.card := by simp

theorem greedySuppliedJointStickyScaleCover_coarseCard_le_active
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (greedySuppliedJointStickyScaleCover P C).coarseCard ≤ active.card := by
  exact occupiedJointParents_card_le_active P C

theorem occupiedJointParents_card_le_blocks_mul_count
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (occupiedJointParents P C).card ≤
      (blocks fine.bodyFamily P).length * C.count := by
  calc
    (occupiedJointParents P C).card ≤
        Fintype.card (JointParentCode P C) :=
      Finset.card_le_univ _
    _ = (blocks fine.bodyFamily P).length * C.count := by simp

theorem greedySuppliedJointStickyScaleCover_coarseCard_le_length_mul_count
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (greedySuppliedJointStickyScaleCover P C).coarseCard ≤
      P.length * C.count := by
  rw [greedySuppliedJointStickyScaleCover_coarseCard]
  simpa only [blocks_length fine.bodyFamily P] using
    occupiedJointParents_card_le_blocks_mul_count P C

#print axioms greedySuppliedJointStickyScaleCover
#print axioms parent_decodes_jointCode
#print axioms fine_mem_decoded_greedyBlock
#print axioms parent_tube_eq_suppliedParentTube
#print axioms fine_carrier_subset_joint_parent
#print axioms occupiedJointParents_card_le_active
#print axioms occupiedJointParents_card_le_blocks_mul_count

end
end Family8GreedySuppliedCoverJointStickyScaleCoverV1
