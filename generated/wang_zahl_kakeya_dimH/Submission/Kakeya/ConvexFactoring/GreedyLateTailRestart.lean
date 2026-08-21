import Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing

/-!
# Late-tail restarts for greedy density partitions

This module restarts a dependent greedy certificate at an actual occurrence,
identifies the restarted initial density with that occurrence's block density,
and proves that its winner is globally maximal for the remaining active set.
The suffix occurrences embed back into the original occurrence order while
preserving their blocks, contained mass, and cardinality.

The density-bucket result uses the canonical family obtained by taking a label
fiber inside a restarted suffix and embedding it back into the original index
type.  It does not identify this family with an externally supplied `Finset`
specified only by having the same least occurrence.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FullConvexMaximalDensity
open GreedyOccurrenceFactorization
open GreedyDensityBucketing

noncomputable section

namespace GreedyLateTailRestart

/-- The dependent greedy suffix beginning at an actual occurrence. -/
def suffixAt {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} :
    {active : Finset ι} →
      (P : GreedyDensityPartition F candidates container active) →
      Fin (blocks F P).length →
      Σ tailActive, GreedyDensityPartition F candidates container tailActive
  | _, .empty, k => Fin.elim0 k
  | active, .step choice hfiber tail, k =>
      Fin.cases ⟨active, .step choice hfiber tail⟩
        (fun k' => suffixAt F tail k') k

/-- The active fine indices at an occurrence. -/
def activeAt {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) : Finset ι :=
  (suffixAt F P k).1

/-- The greedy certificate restarted at an occurrence. -/
def partitionAt {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    GreedyDensityPartition F candidates container (activeAt F P k) :=
  (suffixAt F P k).2

/-- A suffix active set remains inside every ambient set containing the
original active set. -/
theorem activeAt_subset
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F candidates container active)
      (k : Fin (blocks F P).length) {base : Finset ι},
      active ⊆ base → activeAt F P k ⊆ base
  | _, .empty, k, _, _ => Fin.elim0 k
  | active, .step choice hfiber tail, k, base, hactive => by
      induction k using Fin.cases with
      | zero => exact hactive
      | succ k' =>
          exact activeAt_subset F tail k'
            (Finset.sdiff_subset.trans hactive)

/-- The initial density of a restarted suffix is the density of the original
block at the restart occurrence. -/
theorem initialDensity_partitionAt_eq_blockDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
      (k : Fin (blocks F P).length),
      initialDensity F base (partitionAt F P k) =
        blockDensity F (blockAt F P k)
  | _, .empty, k => Fin.elim0 k
  | active, .step choice hfiber tail, k => by
      induction k using Fin.cases with
      | zero =>
          have h := winningDensities_eq_map_blockDensity F base
            (.step choice hfiber tail)
          simp only [winningDensities, blocks, List.map_cons] at h
          have hhead := (List.cons.inj h).1
          simpa [partitionAt, activeAt, suffixAt, initialDensity, blockAt, blocks]
            using hhead
      | succ k' =>
          simpa [partitionAt, activeAt, suffixAt, blockAt, blocks] using
            initialDensity_partitionAt_eq_blockDensity F base tail k'

/-- At every occurrence, the winner is globally maximal for the active set of
the restarted suffix. -/
theorem densityInside_activeAt_le_blockDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active),
      active ⊆ base → ∀ (k : Fin (blocks F P).length) (K : ConvexBody Space),
        densityInside F (activeAt F P k) K ≤
          blockDensity F (blockAt F P k)
  | _, .empty, _, k, _ => Fin.elim0 k
  | active, .step choice hfiber tail, hactive, k, K => by
      induction k using Fin.cases with
      | zero =>
          have hbase : base.Nonempty :=
            (hfiber.mono choice.fiber_subset).mono hactive
          have hmax := maximalDensityChoice_density_ge_all
            choice hbase hactive K
          have hwinner := winningDensities_eq_map_blockDensity F base
            (.step choice hfiber tail)
          simp only [winningDensities, blocks, List.map_cons] at hwinner
          have hhead := (List.cons.inj hwinner).1
          simpa [activeAt, suffixAt, blockAt, blocks] using hmax.trans_eq hhead
      | succ k' =>
          simpa [activeAt, suffixAt, blockAt, blocks] using
            densityInside_activeAt_le_blockDensity F base tail
              (Finset.sdiff_subset.trans hactive) k' K

/-- Restarting at an occurrence leaves exactly the remaining number of
blocks. -/
theorem blocks_partitionAt_length_add
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F candidates container active)
      (k : Fin (blocks F P).length),
      (blocks F (partitionAt F P k)).length + k.val =
        (blocks F P).length
  | _, .empty, k => Fin.elim0 k
  | active, .step choice hfiber tail, k => by
      induction k using Fin.cases with
      | zero => simp [partitionAt, activeAt, suffixAt, blocks]
      | succ k' =>
          have ih := blocks_partitionAt_length_add F tail k'
          change (blocks F (partitionAt F tail k')).length +
              (k'.val + 1) = (blocks F tail).length + 1
          calc
            _ = ((blocks F (partitionAt F tail k')).length + k'.val) + 1 := by
              omega
            _ = (blocks F tail).length + 1 := congrArg Nat.succ ih

/-- Reinsert a suffix occurrence into the original occurrence order. -/
def liftSuffixIndex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length)
    (q : Fin (blocks F (partitionAt F P k)).length) :
    Fin (blocks F P).length :=
  ⟨k.val + q.val, by
    have hlength := blocks_partitionAt_length_add F P k
    have hq := q.isLt
    omega⟩

/-- Reinsertion shifts a suffix position by the restart position. -/
@[simp] theorem liftSuffixIndex_val
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length)
    (q : Fin (blocks F (partitionAt F P k)).length) :
    (liftSuffixIndex F P k q).val = k.val + q.val :=
  rfl

/-- Reinsertion preserves the actual block, not merely its body. -/
theorem blockAt_partitionAt_eq_blockAt_liftSuffixIndex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F candidates container active)
      (k : Fin (blocks F P).length)
      (q : Fin (blocks F (partitionAt F P k)).length),
      blockAt F (partitionAt F P k) q =
        blockAt F P (liftSuffixIndex F P k q)
  | _, .empty, k, _ => Fin.elim0 k
  | active, .step choice hfiber tail, k, q => by
      induction k using Fin.cases with
      | zero =>
          simp only [partitionAt, activeAt, suffixAt]
          unfold blockAt
          congr 1
          apply Fin.ext
          change q.val = (0 : Nat) + q.val
          simp
      | succ k' =>
          have hlift :
              liftSuffixIndex F (.step choice hfiber tail) (Fin.succ k') q =
                Fin.succ (liftSuffixIndex F tail k' q) := by
            apply Fin.ext
            change (k'.val + 1) + q.val = (k'.val + q.val) + 1
            omega
          rw [hlift]
          simpa [partitionAt, activeAt, suffixAt, blockAt, blocks] using
            blockAt_partitionAt_eq_blockAt_liftSuffixIndex F tail k' q

/-- Reinsertion is injective. -/
theorem liftSuffixIndex_injective
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    Function.Injective (liftSuffixIndex F P k) := by
  intro q r hqr
  apply Fin.ext
  have hval := congrArg Fin.val hqr
  rw [liftSuffixIndex_val F P k q, liftSuffixIndex_val F P k r] at hval
  exact Nat.add_left_cancel hval

/-- The occurrence-order embedding of a restarted suffix. -/
def liftSuffixEmbedding
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    Fin (blocks F (partitionAt F P k)).length ↪
      Fin (blocks F P).length :=
  ⟨liftSuffixIndex F P k, liftSuffixIndex_injective F P k⟩

/-- A suffix occurrence body agrees with the corresponding original body. -/
theorem occurrenceFamily_liftSuffixIndex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length)
    (q : Fin (blocks F (partitionAt F P k)).length) :
    occurrenceFamily F P (liftSuffixIndex F P k q) =
      occurrenceFamily F (partitionAt F P k) q := by
  exact congrArg Block.body
    (blockAt_partitionAt_eq_blockAt_liftSuffixIndex F P k q).symm

/-- Contained mass is unchanged when an active finite family is transported
along an embedding. -/
theorem containedMassOn_map_embedding
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (G : ConvexFamily β) (s : Finset α)
    (K : ConvexBody Space) :
    containedMassOn G (s.map e) K =
      containedMassOn (fun i => G (e i)) s K := by
  classical
  unfold containedMassOn
  rw [show s.map e ∩ containedIndices G K =
      (s ∩ containedIndices (fun i => G (e i)) K).map e by
    ext j
    simp only [Finset.mem_inter, Finset.mem_map, mem_containedIndices]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hcontained⟩
      exact ⟨a, ⟨ha, hcontained⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hcontained⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hcontained⟩]
  simp

/-- Katz--Tao bounds transport from an embedded reindexing to its image. -/
theorem isKatzTaoOn_map_embedding
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (G : ConvexFamily β) (s : Finset α) (A : ℝ≥0∞)
    (h : IsKatzTaoOn A (fun i => G (e i)) s) :
    IsKatzTaoOn A G (s.map e) := by
  intro K
  rw [containedMassOn_map_embedding e G s K]
  exact h K

/-- Selected suffix occurrences expressed in the original occurrence index
type. -/
def liftedOccurrences
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length)
    (S : Finset (Fin (blocks F (partitionAt F P k)).length)) :
    Finset (Fin (blocks F P).length) :=
  S.map (liftSuffixEmbedding F P k)

/-- Restarting at `k₀` replaces comparison with the original initial winner by
comparison with the winner at `k₀`.  Selected occurrences are indexed in the
restarted suffix. -/
theorem suffixOccurrenceFamily_isKatzTaoOn_of_first_comparable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) (k₀ : Fin (blocks F P).length)
    (S : Finset (Fin (blocks F (partitionAt F P k₀)).length))
    (δ A : ℝ≥0∞) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞)
    (hlower : ∀ k ∈ S,
      δ ≤ blockDensity F (blockAt F (partitionAt F P k₀) k))
    (hfirst : blockDensity F (blockAt F P k₀) ≤ A * δ) :
    IsKatzTaoOn A (occurrenceFamily F (partitionAt F P k₀)) S := by
  apply occurrenceFamily_isKatzTaoOn_of_comparable
    F base (partitionAt F P k₀)
      (activeAt_subset F P k₀ hactive) S δ A hδ0 hδtop hlower
  simpa [initialDensity_partitionAt_eq_blockDensity F base P k₀] using hfirst

/-- The suffix has a first occurrence because the restart index itself was an
actual original occurrence. -/
theorem partitionAt_blocks_length_pos
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    0 < (blocks F (partitionAt F P k)).length := by
  have hlength := blocks_partitionAt_length_add F P k
  have hk := k.isLt
  omega

/-- The zero position in the restarted suffix. -/
def suffixFirstIndex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    Fin (blocks F (partitionAt F P k)).length :=
  ⟨0, partitionAt_blocks_length_pos F P k⟩

@[simp] theorem liftSuffixIndex_suffixFirstIndex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    liftSuffixIndex F P k (suffixFirstIndex F P k) = k := by
  apply Fin.ext
  simp [suffixFirstIndex]

/-- Every lifted suffix occurrence is at or after the restart occurrence. -/
theorem mem_liftedOccurrences_val_ge
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length)
    (S : Finset (Fin (blocks F (partitionAt F P k)).length))
    {r : Fin (blocks F P).length} (hr : r ∈ liftedOccurrences F P k S) :
    k.val ≤ r.val := by
  rcases Finset.mem_map.mp hr with ⟨q, hq, rfl⟩
  simp [liftSuffixEmbedding]

/-- Embedding the selected suffix positions preserves their exact count. -/
@[simp] theorem card_liftedOccurrences
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length)
    (S : Finset (Fin (blocks F (partitionAt F P k)).length)) :
    (liftedOccurrences F P k S).card = S.card := by
  simp [liftedOccurrences]

/-- The restarted Katz--Tao bound transported back to the original occurrence
index type. -/
theorem liftedSuffixOccurrences_isKatzTaoOn_of_first_comparable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) (k₀ : Fin (blocks F P).length)
    (S : Finset (Fin (blocks F (partitionAt F P k₀)).length))
    (δ A : ℝ≥0∞) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞)
    (hlower : ∀ k ∈ S,
      δ ≤ blockDensity F (blockAt F (partitionAt F P k₀) k))
    (hfirst : blockDensity F (blockAt F P k₀) ≤ A * δ) :
    IsKatzTaoOn A (occurrenceFamily F P) (liftedOccurrences F P k₀ S) := by
  unfold liftedOccurrences
  apply isKatzTaoOn_map_embedding
    (liftSuffixEmbedding F P k₀) (occurrenceFamily F P) S A
  change IsKatzTaoOn A
    (fun q => occurrenceFamily F P (liftSuffixIndex F P k₀ q)) S
  simpa only [occurrenceFamily_liftSuffixIndex] using
    suffixOccurrenceFamily_isKatzTaoOn_of_first_comparable
      F base P hactive k₀ S δ A hδ0 hδtop hlower hfirst

/-- A density bucket in a restarted suffix, expressed in the original
occurrence index type. -/
def liftedSuffixDensityBucket
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (k₀ : Fin (blocks F P).length) (label : ℝ≥0∞ → β) (b : β) :
    Finset (Fin (blocks F P).length) :=
  liftedOccurrences F P k₀
    (occurrenceDensityBucket F base (partitionAt F P k₀) label b)

/-- A restarted density bucket is Katz--Tao under internal lower density and
comparison with its restart winner. -/
theorem liftedSuffixDensityBucket_isKatzTaoOn
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) (k₀ : Fin (blocks F P).length)
    (label : ℝ≥0∞ → β) (b : β) (δ A : ℝ≥0∞)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞)
    (hlower : ∀ ρ, label ρ = b → δ ≤ ρ)
    (hfirst : blockDensity F (blockAt F P k₀) ≤ A * δ) :
    IsKatzTaoOn A (occurrenceFamily F P)
      (liftedSuffixDensityBucket F base P k₀ label b) := by
  apply liftedSuffixOccurrences_isKatzTaoOn_of_first_comparable
    F base P hactive k₀ _ δ A hδ0 hδtop
  · intro q hq
    exact hlower _
      ((mem_occurrenceDensityBucket F base (partitionAt F P k₀) label b q).1 hq)
  · exact hfirst

/-- If the restart winner has the selected label, it is the first occurrence
of the lifted bucket; in particular the preceding theorem is genuinely based
at a selected winner. -/
theorem restart_mem_liftedSuffixDensityBucket
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (k₀ : Fin (blocks F P).length) (label : ℝ≥0∞ → β) (b : β)
    (hlabel : label (blockDensity F (blockAt F P k₀)) = b) :
    k₀ ∈ liftedSuffixDensityBucket F base P k₀ label b := by
  unfold liftedSuffixDensityBucket liftedOccurrences
  apply Finset.mem_map.mpr
  refine ⟨suffixFirstIndex F P k₀, ?_, ?_⟩
  · rw [mem_occurrenceDensityBucket]
    rw [blockAt_partitionAt_eq_blockAt_liftSuffixIndex,
      liftSuffixIndex_suffixFirstIndex]
    exact hlabel
  · exact liftSuffixIndex_suffixFirstIndex F P k₀

/-- A selected restart winner is the least occurrence of its lifted suffix
bucket, and explicit within-bucket density comparability yields Katz--Tao. -/
theorem liftedSuffixDensityBucket_first_min_and_isKatzTaoOn
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) (k₀ : Fin (blocks F P).length)
    (label : ℝ≥0∞ → β) (b : β) (δ A : ℝ≥0∞)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞)
    (hlabel : label (blockDensity F (blockAt F P k₀)) = b)
    (hlower : ∀ ρ, label ρ = b → δ ≤ ρ)
    (hfirst : blockDensity F (blockAt F P k₀) ≤ A * δ) :
    k₀ ∈ liftedSuffixDensityBucket F base P k₀ label b ∧
      (∀ r ∈ liftedSuffixDensityBucket F base P k₀ label b,
        k₀.val ≤ r.val) ∧
      IsKatzTaoOn A (occurrenceFamily F P)
        (liftedSuffixDensityBucket F base P k₀ label b) := by
  refine ⟨restart_mem_liftedSuffixDensityBucket F base P k₀ label b hlabel,
    ?_, liftedSuffixDensityBucket_isKatzTaoOn F base P hactive k₀
      label b δ A hδ0 hδtop hlower hfirst⟩
  intro r hr
  exact mem_liftedOccurrences_val_ge F P k₀
    (occurrenceDensityBucket F base (partitionAt F P k₀) label b) hr

end GreedyLateTailRestart

end

end Submission.Kakeya.ConvexFactoring
