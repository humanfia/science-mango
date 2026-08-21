import Submission.Kakeya.Uniformity.TubeFamily
import Submission.Kakeya.ConvexFactoring.Factorization
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement

open Set
open scoped ENNReal NNReal

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

/-!
# Coarse tube partitions

This module packages a *given* parent assignment between two already
constructed uniform tube families. None of the structures below asserts that
a coarse tube family, parent map, or controlled branching can be constructed
from arbitrary fine tubes.
-/

/-- A supplied partition of the active `δ`-tubes among active `ρ`-tubes.

The two active sets are exactly the refined sets carried by the corresponding
`UniformTubeFamily`s. The function `index.parent` gives the unique parent of
each fine index. Geometric containment, occupation of every active coarse
index, and two-sided approximate uniformity of fiber cardinalities are data,
not existence claims. -/
structure CoarseTubePartition
    {δ ρ : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (fineFamily : UniformTubeFamily δ ι)
    (coarseFamily : UniformTubeFamily ρ κ) where
  scale_le : δ ≤ ρ
  index : IndexFactorization ι κ
  fine_eq_refined : index.fine = fineFamily.refinement.refined
  coarse_eq_refined : index.coarse = coarseFamily.refinement.refined
  coarse_nonempty : index.coarse.Nonempty
  carrier_subset : ∀ i ∈ index.fine,
    (fineFamily.tubes i).carrier ⊆
      (coarseFamily.tubes (index.parent i)).carrier
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

namespace CoarseTubePartition

variable {δ ρ : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily δ ι}
  {coarseFamily : UniformTubeFamily ρ κ}

/-- The active fine indices. -/
def fineIndices (P : CoarseTubePartition fineFamily coarseFamily) : Finset ι :=
  P.index.fine

/-- The active coarse indices. -/
def coarseIndices (P : CoarseTubePartition fineFamily coarseFamily) : Finset κ :=
  P.index.coarse

/-- The active fine indices are precisely the uniform refinement selected by
the fine family. -/
theorem fineIndices_eq_refined
    (P : CoarseTubePartition fineFamily coarseFamily) :
    P.fineIndices = fineFamily.refinement.refined :=
  P.fine_eq_refined

/-- The active coarse indices are precisely the uniform refinement selected by
the coarse family. -/
theorem coarseIndices_eq_refined
    (P : CoarseTubePartition fineFamily coarseFamily) :
    P.coarseIndices = coarseFamily.refinement.refined :=
  P.coarse_eq_refined

/-- A hierarchy step has at least one active coarse tube. -/
theorem coarseIndices_nonempty
    (P : CoarseTubePartition fineFamily coarseFamily) :
    P.coarseIndices.Nonempty :=
  P.coarse_nonempty

/-- The fine indices assigned to an active coarse tube. -/
def fiber (P : CoarseTubePartition fineFamily coarseFamily) (k : κ) : Finset ι :=
  P.index.fiber k

@[simp] theorem mem_fiber
    (P : CoarseTubePartition fineFamily coarseFamily) (i : ι) (k : κ) :
    i ∈ P.fiber k ↔ i ∈ P.fineIndices ∧ P.index.parent i = k :=
  P.index.mem_fiber i k

/-- Membership in two fibers forces their coarse indices to agree. -/
theorem parent_unique
    (P : CoarseTubePartition fineFamily coarseFamily)
    {i : ι} {k l : κ} (hik : i ∈ P.fiber k) (hil : i ∈ P.fiber l) :
    k = l := by
  have hk : P.index.parent i = k := (P.mem_fiber i k).1 hik |>.2
  have hl : P.index.parent i = l := (P.mem_fiber i l).1 hil |>.2
  exact hk.symm.trans hl

/-- Every declared active coarse tube has a nonempty fine fiber. -/
theorem fiber_nonempty
    (P : CoarseTubePartition fineFamily coarseFamily)
    {k : κ} (hk : k ∈ P.coarseIndices) : (P.fiber k).Nonempty := by
  obtain ⟨i, hi, hparent⟩ := P.parent_surjective k hk
  exact ⟨i, (P.mem_fiber i k).2 ⟨hi, hparent⟩⟩

/-- Surjectivity over a nonempty active coarse set makes the active fine set
nonempty as well. -/
theorem fineIndices_nonempty
    (P : CoarseTubePartition fineFamily coarseFamily) :
    P.fineIndices.Nonempty := by
  obtain ⟨k, hk⟩ := P.coarseIndices_nonempty
  obtain ⟨i, hi, _hparent⟩ := P.parent_surjective k hk
  exact ⟨i, hi⟩

/-- The active fibers cover the active fine index set exactly. -/
theorem fibers_cover
    (P : CoarseTubePartition fineFamily coarseFamily) :
    P.coarseIndices.biUnion P.fiber = P.fineIndices :=
  P.index.biUnion_fiber_eq_fine

/-- Fiber cardinalities sum exactly to the number of active fine tubes. -/
theorem card_fine_eq_sum_card_fiber
    (P : CoarseTubePartition fineFamily coarseFamily) :
    P.fineIndices.card = ∑ k ∈ P.coarseIndices, (P.fiber k).card :=
  P.index.card_eq_sum_card_fiber

/-- The partition as a geometric convex factorization, forgetting tube radii
but retaining all active indices and carrier containments. -/
def asConvexFactorization
    (P : CoarseTubePartition fineFamily coarseFamily) :
    ConvexFactorization fineFamily.bodyFamily coarseFamily.bodyFamily where
  index := P.index
  contained := P.carrier_subset

/-- Union of the carriers of the active fine tubes. -/
def fineCarrierUnion
    (P : CoarseTubePartition fineFamily coarseFamily) : Set Space :=
  ⋃ i : {i // i ∈ P.fineIndices}, (fineFamily.tubes i.1).carrier

/-- Union of the carriers of the active coarse tubes. -/
def coarseCarrierUnion
    (P : CoarseTubePartition fineFamily coarseFamily) : Set Space :=
  ⋃ k : {k // k ∈ P.coarseIndices}, (coarseFamily.tubes k.1).carrier

/-- Carrier containment for each parent gives containment of active unions. -/
theorem fineCarrierUnion_subset_coarseCarrierUnion
    (P : CoarseTubePartition fineFamily coarseFamily) :
    P.fineCarrierUnion ⊆ P.coarseCarrierUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let k : {k // k ∈ P.coarseIndices} :=
    ⟨P.index.parent i.1, P.index.parent_mem i.1 i.2⟩
  exact Set.mem_iUnion.mpr ⟨k, P.carrier_subset i.1 i.2 hxi⟩

/-- Number of active fine tube carriers through a point. -/
noncomputable def fineMultiplicity
    (P : CoarseTubePartition fineFamily coarseFamily) (x : Space) : ℕ := by
  classical
  exact (P.fineIndices.filter fun i ↦ x ∈ (fineFamily.tubes i).carrier).card

/-- Number of fine tube carriers in one coarse fiber through a point. -/
noncomputable def fiberMultiplicity
    (P : CoarseTubePartition fineFamily coarseFamily) (k : κ)
    (x : Space) : ℕ := by
  classical
  exact ((P.fiber k).filter fun i ↦ x ∈ (fineFamily.tubes i).carrier).card

private theorem card_filter_eq_sum_indicator
    {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ i ∈ s, if p i then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp_all

/-- Fine pointwise multiplicity is the exact sum of its fiber multiplicities. -/
theorem fineMultiplicity_eq_sum_fiberMultiplicity
    (P : CoarseTubePartition fineFamily coarseFamily) (x : Space) :
    P.fineMultiplicity x =
      ∑ k ∈ P.coarseIndices, P.fiberMultiplicity k x := by
  classical
  rw [fineMultiplicity, card_filter_eq_sum_indicator]
  simp_rw [fiberMultiplicity, card_filter_eq_sum_indicator]
  exact P.index.sum_fiberwise
    (fun i ↦ if x ∈ (fineFamily.tubes i).carrier then 1 else 0)

/-- A fiber multiplicity is bounded by the number of indices in that fiber. -/
theorem fiberMultiplicity_le_card
    (P : CoarseTubePartition fineFamily coarseFamily) (k : κ) (x : Space) :
    P.fiberMultiplicity k x ≤ (P.fiber k).card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The target branching count is retained, up to `branchingLoss`, by every
active fiber. -/
theorem branching_withinFactor_fiber
    (P : CoarseTubePartition fineFamily coarseFamily)
    {k : κ} (hk : k ∈ P.coarseIndices) :
    WithinFactor P.branchingLoss (P.branching : ℝ≥0∞)
      ((P.fiber k).card : ℝ≥0∞) := by
  unfold WithinFactor
  simp only [nsmul_eq_mul]
  exact_mod_cast P.branching_le_loss_mul_fiber k hk

/-- Conversely, every active fiber is retained, up to `branchingLoss`, by the
target branching count. -/
theorem fiber_withinFactor_branching
    (P : CoarseTubePartition fineFamily coarseFamily)
    {k : κ} (hk : k ∈ P.coarseIndices) :
    WithinFactor P.branchingLoss ((P.fiber k).card : ℝ≥0∞)
      (P.branching : ℝ≥0∞) := by
  unfold WithinFactor
  simp only [nsmul_eq_mul]
  exact_mod_cast P.fiber_card_le_loss_mul_branching k hk

/-- Uniform upper branching bounds every pointwise fiber multiplicity. -/
theorem fiberMultiplicity_le_loss_mul_branching
    (P : CoarseTubePartition fineFamily coarseFamily)
    {k : κ} (hk : k ∈ P.coarseIndices) (x : Space) :
    P.fiberMultiplicity k x ≤ P.branchingLoss * P.branching :=
  (P.fiberMultiplicity_le_card k x).trans
    (P.fiber_card_le_loss_mul_branching k hk)

/-- The total number of fine tubes is at most the number of coarse tubes times
the uniform upper branching bound. -/
theorem card_fine_le_coarse_mul_loss_mul_branching
    (P : CoarseTubePartition fineFamily coarseFamily) :
    P.fineIndices.card ≤
      P.coarseIndices.card * (P.branchingLoss * P.branching) := by
  rw [P.card_fine_eq_sum_card_fiber]
  calc
    (∑ k ∈ P.coarseIndices, (P.fiber k).card) ≤
        ∑ _k ∈ P.coarseIndices, P.branchingLoss * P.branching :=
      Finset.sum_le_sum fun k hk ↦
        P.fiber_card_le_loss_mul_branching k hk
    _ = P.coarseIndices.card * (P.branchingLoss * P.branching) := by
      simp

/-- The exact fiber decomposition and uniform fiber bound give a global
pointwise multiplicity bound. -/
theorem fineMultiplicity_le_coarse_mul_loss_mul_branching
    (P : CoarseTubePartition fineFamily coarseFamily) (x : Space) :
    P.fineMultiplicity x ≤
      P.coarseIndices.card * (P.branchingLoss * P.branching) := by
  rw [P.fineMultiplicity_eq_sum_fiberMultiplicity x]
  calc
    (∑ k ∈ P.coarseIndices, P.fiberMultiplicity k x) ≤
        ∑ _k ∈ P.coarseIndices, P.branchingLoss * P.branching :=
      Finset.sum_le_sum fun k hk ↦
        P.fiberMultiplicity_le_loss_mul_branching hk x
    _ = P.coarseIndices.card * (P.branchingLoss * P.branching) := by
      simp

end CoarseTubePartition

/-- A one-step hierarchy containing two uniform families and their supplied
coarse partition. Longer hierarchies can be built by composing such steps while
sharing the intermediate family. -/
structure TubeHierarchy
    (δ ρ : NNReal) (ι κ : Type*) [DecidableEq ι] [DecidableEq κ] where
  fineFamily : UniformTubeFamily δ ι
  coarseFamily : UniformTubeFamily ρ κ
  partition : CoarseTubePartition fineFamily coarseFamily

namespace TubeHierarchy

variable {δ ρ : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The hierarchy's active fine set. -/
def fineIndices (H : TubeHierarchy δ ρ ι κ) : Finset ι :=
  H.partition.fineIndices

/-- The hierarchy's active coarse set. -/
def coarseIndices (H : TubeHierarchy δ ρ ι κ) : Finset κ :=
  H.partition.coarseIndices

/-- The hierarchy inherits exact coverage by parent fibers. -/
theorem fibers_cover (H : TubeHierarchy δ ρ ι κ) :
    H.coarseIndices.biUnion H.partition.fiber = H.fineIndices :=
  H.partition.fibers_cover

/-- The hierarchy inherits containment of the active carrier unions. -/
theorem fineCarrierUnion_subset_coarseCarrierUnion
    (H : TubeHierarchy δ ρ ι κ) :
    H.partition.fineCarrierUnion ⊆ H.partition.coarseCarrierUnion :=
  H.partition.fineCarrierUnion_subset_coarseCarrierUnion

end TubeHierarchy

/-!
This data layer deliberately contains no existence theorem. The geometric
argument must later construct the coarse family, parent assignment, carrier
containments, occupied fibers, branching estimates, and compatibility between
successive scales from the Wang--Zahl hypotheses.
-/

end Submission.Kakeya.ConvexFactoring
