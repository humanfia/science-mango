import Family8Grounding.Family8PlankThickControlMutualContainmentClusteringV2
import Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankThickControlOwnerFiberLogBucketV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# One actual logarithmic owner-fibre bucket

Starting from the lossless mutual-thickening clustering, this module selects
one base-two cardinality class of selected seeds.  The sum of the literal
source shaded masses in its owner fibres retains the full source mass with
exact loss `log₂(card iota) + 1`.  Every retained fibre has one common
branching scale `N`, satisfies `N <= card < 2N`, and still obeys the genuine
`card <= M * theta` thick-control estimate.

V1 failed only a missing definitional unfold and is not imported.\n\nNo slab, tube, or multiplicity conclusion is assumed here.
-/

/-- Literal source shaded mass assigned to one selected owner. -/
def ownerFiberMass
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s : iota) : ENNReal :=
  ∑ i ∈ ownerFiber C s, volume (D.shading.carrier i)

/-- Base-two label of an actual owner-fibre cardinality. -/
def ownerFiberLogCardLabel
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s : iota) :
    Fin (Nat.log 2 (Fintype.card iota) + 1) :=
  ⟨Nat.log 2 (ownerFiber C s).card, by
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    exact Finset.card_le_card (Finset.subset_univ _)⟩

/-- Selected thickening seeds whose owner fibres lie in one logarithmic
cardinality class. -/
def selectedOwnerLogBucket
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) : Finset iota :=
  dyadicFiber C.selected (ownerFiberLogCardLabel C) q

/-- The common lower branching scale of one owner-fibre bucket. -/
def ownerBucketBranching
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) : Nat :=
  2 ^ q.1

theorem mem_selectedOwnerLogBucket
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) (s : iota) :
    s ∈ selectedOwnerLogBucket C q ↔
      s ∈ C.selected ∧ ownerFiberLogCardLabel C s = q := by
  exact mem_dyadicFiber C.selected (ownerFiberLogCardLabel C) q s

/-- Every retained owner fibre has cardinality in the literal common dyadic
window. -/
theorem selectedOwnerLogBucket_card_bounds
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) {s : iota}
    (hs : s ∈ selectedOwnerLogBucket C q) :
    ownerBucketBranching q ≤ (ownerFiber C s).card ∧
      (ownerFiber C s).card < 2 * ownerBucketBranching q := by
  have hsSelected : s ∈ C.selected :=
    (mem_selectedOwnerLogBucket C q s).1 hs |>.1
  have hn0 : (ownerFiber C s).card ≠ 0 :=
    Finset.card_ne_zero.mpr (ownerFiber_nonempty_of_selected C hsSelected)
  have hlabel : ownerFiberLogCardLabel C s = q :=
    (mem_selectedOwnerLogBucket C q s).1 hs |>.2
  have hlog : Nat.log 2 (ownerFiber C s).card = q.1 :=
    congrArg Fin.val hlabel
  constructor
  · unfold ownerBucketBranching
    rw [← hlog]
    exact Nat.pow_log_le_self 2 hn0
  · have hupper :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two (ownerFiber C s).card
    unfold ownerBucketBranching
    rw [hlog] at hupper
    simpa [pow_succ, Nat.mul_comm] using hupper

/-- A single logarithmic fibre-cardinality bucket retains the exact source
shaded-mass partition with the number of labels as loss. -/
theorem exists_selectedOwnerLogBucket_mass_retaining
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) :
    ∃ q : Fin (Nat.log 2 (Fintype.card iota) + 1),
      D.shading.shadingMass ≤
        (Nat.log 2 (Fintype.card iota) + 1 : Nat) *
          ∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s := by
  obtain ⟨q, hq⟩ :=
    exists_large_ennreal_finiteBucket C.selected
      (ownerFiberLogCardLabel C) (ownerFiberMass C)
  refine ⟨q, ?_⟩
  rw [shadingMass_eq_sum_ownerFiber_mass C]
  simpa only [ownerFiberMass, selectedOwnerLogBucket, Fintype.card_fin] using hq

/-- Combined construction: one retained mass bucket, one common positive
branching scale, the two-sided dyadic fibre bounds, and the actual
`M * theta` cap all hold on the same selected seeds. -/
theorem exists_selectedOwnerLogBucket_mass_card_thickControl
    (D : ShadedConvexPlankFamily iota a b) (M theta : NNReal)
    (C : MutualThickeningClustering D theta)
    (hthick : FrostmanThickenedPlankControl D M)
    (hatheta : a / b ≤ theta) (htheta : theta ≤ 1) :
    ∃ q : Fin (Nat.log 2 (Fintype.card iota) + 1),
      D.shading.shadingMass ≤
        (Nat.log 2 (Fintype.card iota) + 1 : Nat) *
          ∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s ∧
      0 < ownerBucketBranching q ∧
      ∀ s ∈ selectedOwnerLogBucket C q,
        ownerBucketBranching q ≤ (ownerFiber C s).card ∧
        (ownerFiber C s).card < 2 * ownerBucketBranching q ∧
        ((ownerFiber C s).card : ENNReal) ≤
          (M : ENNReal) * (theta : ENNReal) := by
  obtain ⟨q, hmass⟩ := exists_selectedOwnerLogBucket_mass_retaining C
  refine ⟨q, hmass, by simp [ownerBucketBranching], ?_⟩
  intro s hs
  have hbounds := selectedOwnerLogBucket_card_bounds C q hs
  exact ⟨hbounds.1, hbounds.2,
    ownerFiber_card_le D M theta C hthick hatheta htheta s⟩

#print axioms mem_selectedOwnerLogBucket
#print axioms selectedOwnerLogBucket_card_bounds
#print axioms exists_selectedOwnerLogBucket_mass_retaining
#print axioms exists_selectedOwnerLogBucket_mass_card_thickControl

end
end Family8PlankThickControlOwnerFiberLogBucketV2
