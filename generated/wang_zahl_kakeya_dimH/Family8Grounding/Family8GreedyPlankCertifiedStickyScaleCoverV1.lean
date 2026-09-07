import Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
import Family8Grounding.Family8PlankCertificateLongTubeCoverV2
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8GreedyPlankCertifiedStickyScaleCoverV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankPairOverlapV2
open Family8PlankCertificateLongTubeCoverV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# A greedy occurrence partition with certified plank winners as a sticky cover

The greedy maximal-density construction already partitions every active fine
index into a unique occurrence block.  If each winning block body is supplied
with an actual `a x b x 1` plank certificate, its certified radius-`b` long
tube is a genuine geometric parent for the entire block.  This module turns
those two independently verified facts into a literal `StickyScaleCover`.

The certificate family is an explicit input.  The final existence theorem
constructs the greedy partition, but still consumes a callback providing the
winner certificates; it makes no claim that arbitrary greedy hull winners
have the required plank dimensions.
-/

universe u v

variable {delta C a b : NNReal}
  {iota : Type u} {kappa : Type v}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}
  {candidates : Finset kappa}
  {container : kappa → ConvexBody Space}

/-- One genuine plank certificate for every actual greedy-step occurrence. -/
def WinnerPlankCertificates
    (P : GreedyDensityPartition fine.bodyFamily candidates container active) :
    Type _ :=
  ∀ k : Fin (blocks fine.bodyFamily P).length,
    PlankDimensionsCertificate C a b (blockAt fine.bodyFamily P k).body

/-- The occurrence-indexed family of certified radius-`b` long tubes. -/
def greedyPlankCoarseFamily
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P) :
    UniformTubeFamily b (Fin (blocks fine.bodyFamily P).length) where
  tubes := fun k ↦ plankCertificateLongTube (cert k)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem greedyPlankCoarseFamily_tubes
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P)
    (k : Fin (blocks fine.bodyFamily P).length) :
    (greedyPlankCoarseFamily P cert).tubes k =
      plankCertificateLongTube (cert k) :=
  rfl

/-- The actual greedy blocks, with their certified long-tube parents, form a
sticky cover of the literal active fine subtype.  Both refinements are full:
every active fine occurrence occurs in one block and every block is nonempty.
-/
def greedyPlankCertifiedStickyScaleCover
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P) :
    StickyScaleCover (fine.restrictTo active) b where
  coarseCard := (blocks fine.bodyFamily P).length
  coarse := greedyPlankCoarseFamily P cert
  activeFine := Finset.univ
  activeCoarse := Finset.univ
  parent := fun i ↦ locate fine.bodyFamily P i.2
  activeFine_eq_refined := rfl
  activeCoarse_eq_refined := rfl
  parent_mem := by simp
  parent_surjective := by
    intro k _hk
    obtain ⟨i, hik⟩ := (blockAt fine.bodyFamily P k).fiber_nonempty
    have hiActive : i ∈ active :=
      blockAt_fiber_subset_active fine.bodyFamily P k hik
    let ii : {i // i ∈ active} := ⟨i, hiActive⟩
    refine ⟨ii, Finset.mem_univ ii, ?_⟩
    change locate fine.bodyFamily P hiActive = k
    exact locate_eq_of_mem_blockAt fine.bodyFamily P hiActive k hik
  carrier_subset := by
    intro i _hi
    have hiBlock :
        i.1 ∈
          (blockAt fine.bodyFamily P (locate fine.bodyFamily P i.2)).fiber :=
      mem_blockAt_locate fine.bodyFamily P i.2
    have hiWinner :
        (fine.bodyFamily i.1 : Set Space) ⊆
          ((blockAt fine.bodyFamily P
            (locate fine.bodyFamily P i.2)).body : Set Space) :=
      (blockAt fine.bodyFamily P
        (locate fine.bodyFamily P i.2)).contained i.1 hiBlock
    exact hiWinner.trans
      (plankCertificate_body_subset_longTube
        (cert (locate fine.bodyFamily P i.2)))

@[simp]
theorem greedyPlankCertifiedStickyScaleCover_coarseCard
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P) :
    (greedyPlankCertifiedStickyScaleCover P cert).coarseCard =
      (blocks fine.bodyFamily P).length :=
  rfl

/-- The constructed coarse cardinality is exactly the recursive greedy
length, rather than merely bounded by it. -/
theorem greedyPlankCertifiedStickyScaleCover_coarseCard_eq_length
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P) :
    (greedyPlankCertifiedStickyScaleCover P cert).coarseCard = P.length := by
  exact blocks_length fine.bodyFamily P

@[simp]
theorem greedyPlankCertifiedStickyScaleCover_activeFine
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P) :
    (greedyPlankCertifiedStickyScaleCover P cert).activeFine = Finset.univ :=
  rfl

@[simp]
theorem greedyPlankCertifiedStickyScaleCover_activeCoarse
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P) :
    (greedyPlankCertifiedStickyScaleCover P cert).activeCoarse = Finset.univ :=
  rfl

@[simp]
theorem greedyPlankCertifiedStickyScaleCover_parent
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P)
    (i : {i // i ∈ active}) :
    (greedyPlankCertifiedStickyScaleCover P cert).parent i =
      locate fine.bodyFamily P i.2 :=
  rfl

/-- The constructed parent's block contains the fine occurrence literally. -/
theorem mem_parent_block
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P)
    (i : {i // i ∈ active}) :
    i.1 ∈ (blockAt fine.bodyFamily P
      ((greedyPlankCertifiedStickyScaleCover P cert).parent i)).fiber := by
  exact mem_blockAt_locate fine.bodyFamily P i.2

/-- Block membership is exactly equality with the constructed parent. -/
theorem mem_block_iff_parent_eq
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P)
    (i : {i // i ∈ active})
    (k : Fin (blocks fine.bodyFamily P).length) :
    i.1 ∈ (blockAt fine.bodyFamily P k).fiber ↔
      (greedyPlankCertifiedStickyScaleCover P cert).parent i = k := by
  constructor
  · intro hik
    exact locate_eq_of_mem_blockAt fine.bodyFamily P i.2 k hik
  · intro hparent
    rw [← hparent]
    exact mem_parent_block P cert i

@[simp]
theorem greedyPlankCertifiedStickyScaleCover_coarse_tube
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P)
    (k : Fin (blocks fine.bodyFamily P).length) :
    (greedyPlankCertifiedStickyScaleCover P cert).coarse.tubes k =
      plankCertificateLongTube (cert k) :=
  rfl

/-- The source tube carrier lies in the certified long tube assigned by its
actual greedy occurrence.  This restates the cover field with its concrete
parent and makes the geometric seam directly reusable. -/
theorem fine_carrier_subset_parent_tube
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P)
    (i : {i // i ∈ active}) :
    (fine.tubes i.1).carrier ⊆
      (plankCertificateLongTube
        (cert (locate fine.bodyFamily P i.2))).carrier := by
  have hiBlock := mem_blockAt_locate fine.bodyFamily P i.2
  exact ((blockAt fine.bodyFamily P
      (locate fine.bodyFamily P i.2)).contained i.1 hiBlock).trans
    (plankCertificate_body_subset_longTube
      (cert (locate fine.bodyFamily P i.2)))

/-! ## Full greedy existence, conditional only on winner certification -/

/-- The full convex maximal-density theorem supplies the partition and its
global cross inequalities.  A caller-provided certification callback supplies
the genuinely geometric plank dimensions for that selected partition.  The
resulting sticky cover has exact greedy length and literal full active sets.

This theorem does **not** prove that greedy hull winners admit such
certificates; that remaining geometric input is visible in `certify`.
-/
theorem exists_fullGreedyCertifiedStickyScaleCover
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (certify : ∀
      (P : GreedyDensityPartition fine.bodyFamily
        (hullCandidates active) (hullContainer fine.bodyFamily) active),
      AllWinnerGlobalCross fine.bodyFamily active P →
        Nonempty
          (WinnerPlankCertificates (C := C) (a := a) (b := b) P)) :
    ∃ P : GreedyDensityPartition fine.bodyFamily
        (hullCandidates active) (hullContainer fine.bodyFamily) active,
      P.coveredIndices = active ∧
      P.length ≤ active.card ∧
      AllWinnerGlobalCross fine.bodyFamily active P ∧
      ∃ cert : WinnerPlankCertificates (C := C) (a := a) (b := b) P,
        (greedyPlankCertifiedStickyScaleCover P cert).coarseCard = P.length ∧
        (greedyPlankCertifiedStickyScaleCover P cert).activeFine =
          Finset.univ ∧
        (greedyPlankCertifiedStickyScaleCover P cert).activeCoarse =
          Finset.univ := by
  obtain ⟨P, hcovered, hlength, hcross⟩ :=
    exists_fullConvexGreedyDensityPartition fine.bodyFamily active
  obtain ⟨cert⟩ := certify P hcross
  refine ⟨P, hcovered, hlength, hcross, cert, ?_, rfl, rfl⟩
  exact greedyPlankCertifiedStickyScaleCover_coarseCard_eq_length P cert

#print axioms greedyPlankCertifiedStickyScaleCover
#print axioms greedyPlankCertifiedStickyScaleCover_coarseCard_eq_length
#print axioms mem_parent_block
#print axioms mem_block_iff_parent_eq
#print axioms fine_carrier_subset_parent_tube
#print axioms exists_fullGreedyCertifiedStickyScaleCover

end
end Family8GreedyPlankCertifiedStickyScaleCoverV1
