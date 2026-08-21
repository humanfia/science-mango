import Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
import Submission.Kakeya.ConvexFactoring.Factorization

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FullConvexMaximalDensity

noncomputable section

/-!
# Occurrence-indexed greedy factorization

Each recursive greedy step becomes a separate list occurrence.  Coarse indices
are positions in that list, so equal winner bodies arising at different steps
remain distinct coarse-family occurrences.
-/

namespace GreedyOccurrenceFactorization

/-- The geometric data carried by one actual greedy extraction step. -/
structure Block {ι : Type*} (F : ConvexFamily ι) where
  fiber : Finset ι
  body : ConvexBody Space
  fiber_nonempty : fiber.Nonempty
  contained : ∀ i ∈ fiber, (F i : Set Space) ⊆ (body : Set Space)

/-- The ordered list of actual greedy-step occurrences. -/
def blocks {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} :
    {active : Finset ι} →
      GreedyDensityPartition F candidates container active → List (Block F)
  | _, .empty => []
  | _, .step choice hfiber tail =>
      { fiber := choice.fiber
        body := container choice.index
        fiber_nonempty := hfiber
        contained := fun _i hi ↦ choice.body_subset_container hi } ::
        blocks F tail

/-- The number of occurrence blocks is exactly the recursive greedy length. -/
theorem blocks_length {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    (blocks F P).length = P.length := by
  induction P with
  | empty => rfl
  | step choice hfiber tail ih =>
      simp [blocks, GreedyDensityPartition.length, ih]

/-- The block at an occurrence position. -/
def blockAt {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) : Block F :=
  (blocks F P).get k

/-- Locate an active fine index in the unique recursive step that removes it. -/
def locate {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} :
    {active : Finset ι} →
      (P : GreedyDensityPartition F candidates container active) →
      {i : ι} → i ∈ active → Fin (blocks F P).length
  | _, .empty, _, hi => by simp at hi
  | _, .step choice hfiber tail, i, hi =>
      if hifiber : i ∈ choice.fiber then
        ⟨0, by simp [blocks]⟩
      else
        Fin.succ (locate F tail (Finset.mem_sdiff.mpr ⟨hi, hifiber⟩))

theorem mem_blockAt_locate {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F candidates container active)
      {i : ι} (hi : i ∈ active),
      i ∈ (blockAt F P (locate F P hi)).fiber
  | _, .empty, _, hi => by simp at hi
  | _, .step choice hfiber tail, i, hi => by
      by_cases hifiber : i ∈ choice.fiber
      · simp [locate, hifiber, blockAt, blocks]
      · have hitail : i ∈ _ \ choice.fiber :=
          Finset.mem_sdiff.mpr ⟨hi, hifiber⟩
        simpa [locate, hifiber, blockAt, blocks] using
          mem_blockAt_locate F tail hitail

theorem blockAt_fiber_subset_active
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F candidates container active)
      (k : Fin (blocks F P).length),
      (blockAt F P k).fiber ⊆ active
  | _, .empty, k => Fin.elim0 k
  | _, .step choice hfiber tail, k => by
      refine Fin.cases ?_ (fun k' ↦ ?_) k
      · simpa [blockAt, blocks] using choice.fiber_subset
      · simpa [blockAt, blocks] using
          (blockAt_fiber_subset_active F tail k').trans Finset.sdiff_subset

/-- Membership in an occurrence block determines that occurrence uniquely. -/
theorem locate_eq_of_mem_blockAt
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F candidates container active)
      {i : ι} (hi : i ∈ active) (k : Fin (blocks F P).length),
      i ∈ (blockAt F P k).fiber → locate F P hi = k
  | _, .empty, _, hi, _, _ => by simp at hi
  | _, .step choice hfiber tail, i, hi, k, hik => by
      induction k using Fin.cases with
      | zero =>
        have hifiber : i ∈ choice.fiber := by
          simpa [blockAt, blocks] using hik
        apply Fin.ext
        simp [locate, hifiber]
      | succ k' =>
        have hitailBlock : i ∈ (blockAt F tail k').fiber := by
          simpa [blockAt, blocks] using hik
        have hitail := blockAt_fiber_subset_active F tail k' hitailBlock
        have hnot : i ∉ choice.fiber := (Finset.mem_sdiff.mp hitail).2
        have hrec := locate_eq_of_mem_blockAt F tail hitail k' hitailBlock
        apply Fin.ext
        simp [locate, hnot, hrec]

/-- Total parent map into an inhabited occurrence type.  Active indices map to
their actual occurrence; inactive indices map to the inactive marker `none`. -/
def parent {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (i : ι) : Option (Fin (blocks F P).length) :=
  if hi : i ∈ active then some (locate F P hi) else none

theorem parent_eq_some_locate {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    {i : ι} (hi : i ∈ active) :
    parent F P i = some (locate F P hi) := by
  simp [parent, hi]

/-- For an active fine index, block membership is exactly equality with its
parent occurrence. -/
theorem mem_blockAt_iff_parent_eq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    {i : ι} (hi : i ∈ active) (k : Fin (blocks F P).length) :
    i ∈ (blockAt F P k).fiber ↔ parent F P i = some k := by
  constructor
  · intro hik
    rw [parent_eq_some_locate F P hi]
    exact congrArg some (locate_eq_of_mem_blockAt F P hi k hik)
  · intro hparent
    rw [parent_eq_some_locate F P hi] at hparent
    have hlocate : locate F P hi = k := Option.some.inj hparent
    rw [← hlocate]
    exact mem_blockAt_locate F P hi

/-- Every active index lies in exactly one occurrence block. -/
theorem existsUnique_blockAt
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    {i : ι} (hi : i ∈ active) :
    ∃! k : Fin (blocks F P).length, i ∈ (blockAt F P k).fiber := by
  refine ⟨locate F P hi, mem_blockAt_locate F P hi, ?_⟩
  intro k hk
  exact (locate_eq_of_mem_blockAt F P hi k hk).symm

/-- The coarse family is indexed by greedy-step occurrences, not by values of
the winner bodies. The inactive `none` index supplies a harmless singleton,
so this remains a family even when there are no occurrences. -/
def coarseFamily {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    ConvexFamily (Option (Fin (blocks F P).length))
  | none => singletonBody 0
  | some k => (blockAt F P k).body

/-- Exactly the genuine greedy-step occurrences are active coarse indices. -/
def occurrenceIndices {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    Finset (Option (Fin (blocks F P).length)) :=
  Finset.univ.image some

/-- Occurrence-indexed combinatorial factorization extracted from a greedy
partition, including the empty one. -/
def indexFactorization {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    IndexFactorization ι (Option (Fin (blocks F P).length)) where
  fine := active
  coarse := occurrenceIndices F P
  parent := parent F P
  parent_mem := by
    intro i hi
    rw [parent_eq_some_locate F P hi]
    simp [occurrenceIndices]

/-- The geometric convex factorization extracted from the actual greedy
partition. -/
def convexFactorization {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    ConvexFactorization F (coarseFamily F P) where
  index := indexFactorization F P
  contained := by
    intro i hi
    have hparent := parent_eq_some_locate F P hi
    change (F i : Set Space) ⊆
      (coarseFamily F P (parent F P i) : Set Space)
    rw [hparent]
    exact (blockAt F P (locate F P hi)).contained i
      (mem_blockAt_locate F P hi)

@[simp] theorem indexFactorization_fine
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    (indexFactorization F P).fine = active :=
  rfl

@[simp] theorem indexFactorization_coarse
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    (indexFactorization F P).coarse = occurrenceIndices F P :=
  rfl

theorem indexFactorization_fiber_eq_blockAt
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (k : Fin (blocks F P).length) :
    (indexFactorization F P).fiber (some k) = (blockAt F P k).fiber := by
  ext i
  rw [IndexFactorization.mem_fiber]
  constructor
  · rintro ⟨hi, hparent⟩
    exact (mem_blockAt_iff_parent_eq F P hi k).2 hparent
  · intro hik
    have hi := blockAt_fiber_subset_active F P k hik
    exact ⟨hi, (mem_blockAt_iff_parent_eq F P hi k).1 hik⟩

/-- The actual occurrence blocks cover the active fine set exactly. -/
theorem biUnion_blockAt_eq_active
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    Finset.univ.biUnion (fun k ↦ (blockAt F P k).fiber) = active := by
  ext i
  constructor
  · intro hi
    obtain ⟨k, _hk, hik⟩ := Finset.mem_biUnion.mp hi
    exact blockAt_fiber_subset_active F P k hik
  · intro hi
    exact Finset.mem_biUnion.mpr
      ⟨locate F P hi, Finset.mem_univ _, mem_blockAt_locate F P hi⟩

/-- The number of active coarse occurrences is exactly the greedy length. -/
theorem coarse_card_eq_length
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active) :
    (indexFactorization F P).coarse.card = P.length := by
  rw [indexFactorization_coarse, occurrenceIndices]
  rw [Finset.card_image_of_injective _ (fun _ _ h ↦ Option.some.inj h)]
  simpa using blocks_length F P

/-- The induced coarse shading has exactly the active fine shaded union. -/
theorem inducedShading_shadedUnion_eq_active
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    ((convexFactorization F P).inducedShading Y).shadedUnion =
      (IndexedShadingRefinement.restrictTo Y active).shading.shadedUnion := by
  exact (convexFactorization F P).inducedShading_shadedUnion_eq Y

/-- Total active shaded mass decomposes exactly as the sum over occurrence
fibers.  This counts overlaps with their original fine-index multiplicity. -/
theorem activeShadingMass_eq_sum_fiberMass
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    (∑ i ∈ active, volume (Y.carrier i)) =
      ∑ k : Fin (blocks F P).length,
        ∑ i ∈ (blockAt F P k).fiber, volume (Y.carrier i) := by
  calc
    (∑ i ∈ active, volume (Y.carrier i)) =
        ∑ k ∈ (indexFactorization F P).coarse,
          ∑ i ∈ (indexFactorization F P).fiber k,
            volume (Y.carrier i) :=
      (indexFactorization F P).sum_fiberwise
        (fun i ↦ volume (Y.carrier i))
    _ = _ := by
      rw [indexFactorization_coarse, occurrenceIndices]
      rw [Finset.sum_image]
      · simp_rw [indexFactorization_fiber_eq_blockAt F P]
      · intro a _ b _ hab
        exact Option.some.inj hab

/-- Actual greedy existence yields an occurrence-indexed convex
factorization; none of the factorization properties are assumed as fields of
the existence statement. -/
theorem exists_occurrenceIndexedConvexFactorization
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (active : Finset ι) :
    ∃ P : GreedyDensityPartition F (hullCandidates active) (hullContainer F) active,
      (convexFactorization F P).index.fine = active ∧
      (convexFactorization F P).index.coarse.card = P.length ∧
      (∀ i ∈ active,
        ∃! k : Fin (blocks F P).length, i ∈ (blockAt F P k).fiber) ∧
      ∀ i ∈ active,
        (F i : Set Space) ⊆
          (coarseFamily F P ((convexFactorization F P).index.parent i) : Set Space) := by
  obtain ⟨P, _hcover, _hlength, _hcross⟩ :=
    exists_fullConvexGreedyDensityPartition F active
  refine ⟨P, rfl, coarse_card_eq_length F P, ?_, ?_⟩
  · intro i hi
    exact existsUnique_blockAt F P hi
  · intro i hi
    exact (convexFactorization F P).contained i hi


/-- Winning active densities, in the same recursive occurrence order as
`blocks`. -/
def winningDensities {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    {active : Finset ι} →
      GreedyDensityPartition F (hullCandidates base) (hullContainer F) active →
        List ℝ≥0∞
  | _, .empty => []
  | active, .step choice _ tail =>
      densityInside F active (hullContainer F choice.index) ::
        winningDensities F base tail

theorem winningDensities_length
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active) :
    (winningDensities F base P).length = P.length := by
  induction P with
  | empty => rfl
  | step choice hfiber tail ih =>
      simp [winningDensities, GreedyDensityPartition.length, ih]

/-- Every density occurring later in a greedy tail is bounded by the current
winner's globally maximal density. -/
theorem winningDensities_le_choice
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    ∀ {active tailActive : Finset ι}
      (choice : MaximalDensityChoice F active
        (hullCandidates base) (hullContainer F))
      (_hfiber : choice.fiber.Nonempty)
      (tail : GreedyDensityPartition F (hullCandidates base) (hullContainer F)
        tailActive)
      (_hactive : active ⊆ base) (_htail : tailActive ⊆ active) {ρ : ℝ≥0∞},
      ρ ∈ winningDensities F base tail →
        ρ ≤ densityInside F active (hullContainer F choice.index)
  | _, _, choice, _hfiber, .empty, _hactive, _htail, ρ, hρ => by
      simp [winningDensities] at hρ
  | active, tailActive, choice, hfiber, .step next hnext rest,
      hactive, htail, ρ, hρ => by
      simp only [winningDensities, List.mem_cons] at hρ
      have hbase : base.Nonempty :=
        (hfiber.mono choice.fiber_subset).mono hactive
      have hnext_le :
          densityInside F tailActive
              (hullContainer F next.index) ≤
            densityInside F active (hullContainer F choice.index) :=
        (densityInside_mono F htail
          (hullContainer F next.index)).trans
          (maximalDensityChoice_density_ge_all choice hbase hactive
            (hullContainer F next.index))
      rcases hρ with rfl | hρ
      · exact hnext_le
      · exact (winningDensities_le_choice F base next hnext rest
          (htail.trans hactive) Finset.sdiff_subset hρ).trans hnext_le

/-- Along the recursive extraction order, winning densities are monotonically
nonincreasing. -/
theorem winningDensities_pairwise_ge_of_subset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) :
    ∀ {active : Finset ι}
      (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active),
      active ⊆ base →
        List.Pairwise (· ≥ ·) (winningDensities F base P)
  | _, .empty, _ => by simp [winningDensities]
  | _, .step choice hfiber tail, hactive => by
      rw [winningDensities, List.pairwise_cons]
      exact ⟨fun _ hρ ↦ winningDensities_le_choice F base choice hfiber tail hactive
          Finset.sdiff_subset hρ,
        winningDensities_pairwise_ge_of_subset F base tail
          (Finset.sdiff_subset.trans hactive)⟩
end GreedyOccurrenceFactorization

end

end Submission.Kakeya.ConvexFactoring
