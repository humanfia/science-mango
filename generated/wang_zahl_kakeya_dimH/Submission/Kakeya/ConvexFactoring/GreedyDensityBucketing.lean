import Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
import Submission.Kakeya.ConvexFactoring.ActiveNonConcentration
import Submission.Kakeya.Uniformity.Pigeonhole

/-!
# Greedy density bucketing and coarse Katz--Tao estimates

This file connects the ordered greedy occurrences to finite density buckets.
It retains exact finite bucket decompositions and explicit bucket-count losses,
derives active Frostman estimates at every occurrence from the global greedy
cross inequality, and proves a coarse Katz--Tao estimate from explicit winner
density comparison hypotheses.

The mass and cardinality selection theorems produce separate bucket witnesses;
no common witness is asserted without an additional uniformity input.  The
Katz--Tao estimate compares the selected density lower bound with the initial
winner density.  A restart on a later greedy tail is not part of this module.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FullConvexMaximalDensity
open GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity

noncomputable section

namespace GreedyDensityBucketing

/-- Total indexed fine mass carried by one actual occurrence block. -/
def blockMass {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (B : Block F) : ℝ≥0∞ :=
  ∑ i ∈ B.fiber, volume (F i : Set Space)

/-- Density of an occurrence block in its winning body. -/
def blockDensity {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (B : Block F) : ℝ≥0∞ :=
  blockMass F B / volume (B.body : Set Space)

/-- The occurrence family without the inactive `Option.none` marker. -/
def occurrenceFamily {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    ConvexFamily (Fin (blocks F P).length) :=
  fun k ↦ (blockAt F P k).body

/-- The official winning-density list is exactly the block-density list. -/
theorem winningDensities_eq_map_blockDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active) :
    winningDensities F base P = (blocks F P).map (blockDensity F) := by
  induction P with
  | empty => rfl
  | @step current choice hfiber tail ih =>
      simp only [winningDensities, blocks, List.map_cons]
      rw [ih]
      congr 1

/-- Block densities are nonincreasing in occurrence order. -/
theorem map_blockDensity_pairwise_ge_of_subset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) :
    List.Pairwise (· ≥ ·) ((blocks F P).map (blockDensity F)) := by
  rw [← winningDensities_eq_map_blockDensity F base P]
  exact winningDensities_pairwise_ge_of_subset F base P hactive

/-- Extract the global cross estimate at an arbitrary occurrence. -/
theorem allWinnerGlobalCross_blockAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active),
      AllWinnerGlobalCross F base P →
      ∀ k : Fin (blocks F P).length, ∀ K : ConvexBody Space,
        massInside F (blockAt F P k).fiber K *
            volume ((blockAt F P k).body : Set Space) ≤
          massInside F (blockAt F P k).fiber (blockAt F P k).body *
            volume (K : Set Space)
  | _, .empty, _, k, _ => Fin.elim0 k
  | _, .step choice hfiber tail, hcross, k, K => by
      induction k using Fin.cases with
      | zero =>
          simpa [blockAt, blocks] using hcross.1 K
      | succ k' =>
          simpa [blockAt, blocks] using
            allWinnerGlobalCross_blockAt F base tail hcross.2 k' K

/-- Every actual greedy occurrence is an active constant-one Frostman family
inside its winning body; this is derived from global cross, not stored. -/
theorem blockAt_isFrostmanOn_one_of_subset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) (k : Fin (blocks F P).length) :
    IsFrostmanOn 1 F (blockAt F P k).fiber (blockAt F P k).body := by
  apply isFrostmanOn_one_of_globalCross
  · exact (blockAt F P k).contained
  · exact allWinnerGlobalCross_blockAt F base P
      (allWinnerGlobalCross_of_subset F base P hactive) k

/-- Exact finite decomposition of an `ENNReal` weight across all buckets. -/
theorem sum_eq_sum_finiteBuckets
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (s : Finset α) (label : α → β) (w : α → ℝ≥0∞) :
    (∑ i ∈ s, w i) =
      ∑ b : β, ∑ i ∈ dyadicFiber s label b, w i := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := s) (t := (Finset.univ : Finset β)) (g := label)
    (fun i hi ↦ Finset.mem_univ (label i)) w

/-- Exact finite cardinality decomposition across all buckets. -/
theorem card_eq_sum_card_finiteBuckets
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (s : Finset α) (label : α → β) :
    s.card = ∑ b : β, (dyadicFiber s label b).card := by
  simpa [dyadicFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := s) (t := (Finset.univ : Finset β)) (f := label)
      (fun i hi ↦ Finset.mem_univ (label i)))

/-- Some finite bucket retains `ENNReal` mass with the exact bucket-count
loss. -/
theorem exists_large_ennreal_finiteBucket
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (label : α → β) (w : α → ℝ≥0∞) :
    ∃ b : β,
      (∑ i ∈ s, w i) ≤
        (Fintype.card β : ℝ≥0∞) *
          ∑ i ∈ dyadicFiber s label b, w i := by
  classical
  let fiberWeight : β → ℝ≥0∞ := fun b ↦
    ∑ i ∈ dyadicFiber s label b, w i
  obtain ⟨b, _hb, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset β) fiberWeight
      Finset.univ_nonempty
  refine ⟨b, ?_⟩
  calc
    (∑ i ∈ s, w i) = ∑ b' : β, fiberWeight b' := by
      exact sum_eq_sum_finiteBuckets s label w
    _ ≤ ∑ _b' : β, fiberWeight b := by
      apply Finset.sum_le_sum
      intro b' hb'
      exact hmax b' hb'
    _ = (Fintype.card β : ℝ≥0∞) *
        ∑ i ∈ dyadicFiber s label b, w i := by
      simp [fiberWeight, nsmul_eq_mul]

/-- Some finite bucket retains cardinality with the exact bucket-count loss. -/
theorem exists_large_card_finiteBucket
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (label : α → β) :
    ∃ b : β,
      s.card ≤ Fintype.card β * (dyadicFiber s label b).card := by
  classical
  let fiberCard : β → ℕ := fun b ↦ (dyadicFiber s label b).card
  obtain ⟨b, _hb, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset β) fiberCard
      Finset.univ_nonempty
  refine ⟨b, ?_⟩
  calc
    s.card = ∑ b' : β, fiberCard b' := by
      exact card_eq_sum_card_finiteBuckets s label
    _ ≤ ∑ _b' : β, fiberCard b := by
      apply Finset.sum_le_sum
      intro b' hb'
      exact hmax b' hb'
    _ = Fintype.card β * (dyadicFiber s label b).card := by
      simp [fiberCard]

/-- Occurrence positions whose winning density lies in one specified finite
bucket. -/
def occurrenceDensityBucket
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    {β : Type*} [DecidableEq β] (label : ℝ≥0∞ → β) (b : β) :
    Finset (Fin (blocks F P).length) :=
  dyadicFiber Finset.univ
    (fun k ↦ label (blockDensity F (blockAt F P k))) b

@[simp] theorem mem_occurrenceDensityBucket
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    {β : Type*} [DecidableEq β] (label : ℝ≥0∞ → β) (b : β)
    (k : Fin (blocks F P).length) :
    k ∈ occurrenceDensityBucket F base P label b ↔
      label (blockDensity F (blockAt F P k)) = b := by
  simp [occurrenceDensityBucket]

/-- A density bucket retaining block mass up to the exact number of labels. -/
theorem exists_occurrenceDensityBucket_mass_loss
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (label : ℝ≥0∞ → β) :
    ∃ b : β,
      (∑ k : Fin (blocks F P).length, blockMass F (blockAt F P k)) ≤
        (Fintype.card β : ℝ≥0∞) *
          ∑ k ∈ occurrenceDensityBucket F base P label b,
            blockMass F (blockAt F P k) := by
  simpa [occurrenceDensityBucket] using
    (exists_large_ennreal_finiteBucket
      (Finset.univ : Finset (Fin (blocks F P).length))
      (fun k ↦ label (blockDensity F (blockAt F P k)))
      (fun k ↦ blockMass F (blockAt F P k)))

/-- A density bucket retaining occurrence count up to the exact number of
labels. -/
theorem exists_occurrenceDensityBucket_card_loss
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (label : ℝ≥0∞ → β) :
    ∃ b : β,
      (blocks F P).length ≤
        Fintype.card β * (occurrenceDensityBucket F base P label b).card := by
  simpa [occurrenceDensityBucket] using
    (exists_large_card_finiteBucket
      (Finset.univ : Finset (Fin (blocks F P).length))
      (fun k ↦ label (blockDensity F (blockAt F P k))))

/-- The initial winning density, with value zero for the empty partition. -/
def initialDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    {active : Finset ι} →
      GreedyDensityPartition F (hullCandidates base) (hullContainer F) active →
        ℝ≥0∞
  | _, .empty => 0
  | active, .step choice _ _ =>
      densityInside F active (hullContainer F choice.index)

/-- Selected occurrence positions whose bodies lie in a test body. -/
def containedOccurrences
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) (K : ConvexBody Space) :
    Finset (Fin (blocks F P).length) := by
  classical
  exact S.filter fun k ↦
    ((blockAt F P k).body : Set Space) ⊆ (K : Set Space)

@[simp] theorem mem_containedOccurrences
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) (K : ConvexBody Space)
    (k : Fin (blocks F P).length) :
    k ∈ containedOccurrences F P S K ↔
      k ∈ S ∧ ((blockAt F P k).body : Set Space) ⊆ (K : Set Space) := by
  classical
  simp [containedOccurrences]

/-- Active coarse mass is the sum over selected occurrence bodies contained
in the test body. -/
theorem containedMassOn_occurrenceFamily_eq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) (K : ConvexBody Space) :
    containedMassOn (occurrenceFamily F P) S K =
      ∑ k ∈ containedOccurrences F P S K,
        volume ((blockAt F P k).body : Set Space) := by
  classical
  unfold containedMassOn containedIndices containedOccurrences
  simp only [occurrenceFamily]
  apply Finset.sum_congr
  · ext k
    simp
  · intro k hk
    rfl

/-- Distinct occurrence positions have disjoint fine fibers. -/
theorem blockAt_fibers_pairwiseDisjoint
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) :
    (↑S : Set (Fin (blocks F P).length)).PairwiseDisjoint
      (fun k ↦ (blockAt F P k).fiber) := by
  intro k hk l hl hkl
  apply Finset.disjoint_left.mpr
  intro i hik hil
  apply hkl
  have hi : i ∈ active := blockAt_fiber_subset_active F P k hik
  have hk' := locate_eq_of_mem_blockAt F P hi k hik
  have hl' := locate_eq_of_mem_blockAt F P hi l hil
  exact hk'.symm.trans hl'

/-- The full masses of selected blocks contained in `K` are bounded by the
original active fine mass in `K`. -/
theorem sum_blockMass_le_activeMassInside
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) (K : ConvexBody Space) :
    (∑ k ∈ containedOccurrences F P S K,
      blockMass F (blockAt F P k)) ≤ massInside F active K := by
  classical
  let T := containedOccurrences F P S K
  have hdisj := blockAt_fibers_pairwiseDisjoint F P T
  have hsubset : T.biUnion (fun k ↦ (blockAt F P k).fiber) ⊆
      indicesInside F active K := by
    intro i hi
    obtain ⟨k, hkT, hik⟩ := Finset.mem_biUnion.mp hi
    have hkBody : ((blockAt F P k).body : Set Space) ⊆ (K : Set Space) :=
      (mem_containedOccurrences F P S K k).1 hkT |>.2
    rw [mem_indicesInside]
    exact ⟨blockAt_fiber_subset_active F P k hik,
      ((blockAt F P k).contained i hik).trans hkBody⟩
  change (∑ k ∈ T, blockMass F (blockAt F P k)) ≤ massInside F active K
  calc
    (∑ k ∈ T, blockMass F (blockAt F P k)) =
        ∑ k ∈ T, ∑ i ∈ (blockAt F P k).fiber,
          volume (F i : Set Space) := by rfl
    _ = ∑ i ∈ T.biUnion (fun k ↦ (blockAt F P k).fiber),
          volume (F i : Set Space) := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ i ∈ indicesInside F active K, volume (F i : Set Space) :=
      Finset.sum_le_sum_of_subset hsubset
    _ = massInside F active K := rfl

/-- A lower density turns block volume into block fine mass, including the
zero-volume case. -/
theorem lower_mul_volume_le_blockMass
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι)
    (B : Block F) (δ : ℝ≥0∞) (hlower : δ ≤ blockDensity F B) :
    δ * volume (B.body : Set Space) ≤ blockMass F B := by
  by_cases hzero : volume (B.body : Set Space) = 0
  · simp [hzero]
  · exact (ENNReal.le_div_iff_mul_le (Or.inl hzero)
      (Or.inl B.body.isCompact.measure_lt_top.ne)).1 hlower

/-- The first greedy winner bounds the full current active mass in every
convex test body. -/
theorem activeMassInside_le_initialDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active),
      active ⊆ base → ∀ K : ConvexBody Space,
        massInside F active K ≤ initialDensity F base P * volume (K : Set Space)
  | _, .empty, _, K => by simp [massInside, indicesInside, initialDensity]
  | active, .step choice hfiber tail, hactive, K => by
      have hbase : base.Nonempty :=
        (hfiber.mono choice.fiber_subset).mono hactive
      by_cases hzero : volume (K : Set Space) = 0
      · rw [massInside_eq_zero_of_volume_eq_zero F active K hzero, hzero]
        simp
      · exact (ENNReal.div_le_iff_le_mul (Or.inl hzero)
          (Or.inl K.isCompact.measure_lt_top.ne)).1
            (maximalDensityChoice_density_ge_all choice hbase hactive K)

/-- Explicit density comparability implies a coarse occurrence Katz--Tao
bound; the Katz--Tao conclusion is derived rather than assumed. -/
theorem occurrenceFamily_isKatzTaoOn_of_comparable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base)
    (S : Finset (Fin (blocks F P).length)) (δ A : ℝ≥0∞)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞)
    (hlower : ∀ k ∈ S, δ ≤ blockDensity F (blockAt F P k))
    (hupper : initialDensity F base P ≤ A * δ) :
    IsKatzTaoOn A (occurrenceFamily F P) S := by
  intro K
  rw [containedMassOn_occurrenceFamily_eq F P S K]
  apply (ENNReal.mul_le_mul_iff_left hδ0 hδtop).mp
  calc
    (∑ k ∈ containedOccurrences F P S K,
        volume ((blockAt F P k).body : Set Space)) * δ =
        ∑ k ∈ containedOccurrences F P S K,
          δ * volume ((blockAt F P k).body : Set Space) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ac_rfl
    _ ≤ ∑ k ∈ containedOccurrences F P S K,
          blockMass F (blockAt F P k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact lower_mul_volume_le_blockMass F (blockAt F P k) δ
        (hlower k ((mem_containedOccurrences F P S K k).1 hk).1)
    _ ≤ massInside F active K := sum_blockMass_le_activeMassInside F P S K
    _ ≤ initialDensity F base P * volume (K : Set Space) :=
      activeMassInside_le_initialDensity F base P hactive K
    _ ≤ (A * δ) * volume (K : Set Space) := by gcongr
    _ = (A * volume (K : Set Space)) * δ := by ac_rfl

/-- The marker-free occurrence family agrees with the existing coarse family
at every genuine occurrence. -/
theorem occurrenceFamily_eq_coarseFamily_some
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    occurrenceFamily F P k = coarseFamily F P (some k) :=
  rfl

/-- A selected density bucket is coarse Katz--Tao once its interval supplies
the explicit lower and initial-winner comparison bounds. -/
theorem occurrenceDensityBucket_isKatzTaoOn
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) (label : ℝ≥0∞ → β) (b : β)
    (δ A : ℝ≥0∞) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞)
    (hlower : ∀ ρ, label ρ = b → δ ≤ ρ)
    (hupper : initialDensity F base P ≤ A * δ) :
    IsKatzTaoOn A (occurrenceFamily F P)
      (occurrenceDensityBucket F base P label b) := by
  apply occurrenceFamily_isKatzTaoOn_of_comparable
    F base P hactive _ δ A hδ0 hδtop
  · intro k hk
    exact hlower _ ((mem_occurrenceDensityBucket F base P label b k).1 hk)
  · exact hupper

end GreedyDensityBucketing

end

end Submission.Kakeya.ConvexFactoring
