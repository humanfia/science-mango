import Submission.Kakeya.ConvexFactoring.NonConcentration
import Submission.Kakeya.ConvexFactoring.IndexPartition

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Maximal density among finitely many candidate containers

This file deliberately makes the candidate family finite.  It proves no
compactness or attainment statement for the type of all convex bodies.
-/

/-- The active indices whose bodies are contained in `K`. -/
def indicesInside {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι) (K : ConvexBody Space) : Finset ι := by
  classical
  exact active.filter fun i ↦ (F i : Set Space) ⊆ (K : Set Space)

@[simp] theorem mem_indicesInside {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι) (K : ConvexBody Space) (i : ι) :
    i ∈ indicesInside F active K ↔
      i ∈ active ∧ (F i : Set Space) ⊆ (K : Set Space) := by
  classical
  simp [indicesInside]

theorem indicesInside_subset {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι) (K : ConvexBody Space) :
    indicesInside F active K ⊆ active := by
  classical
  exact Finset.filter_subset _ _

/-- Total volume, counting repetitions, of the active bodies contained in `K`. -/
def massInside {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι) (K : ConvexBody Space) : ℝ≥0∞ :=
  ∑ i ∈ indicesInside F active K, volume (F i : Set Space)

/-- Density of an active finite subfamily in one candidate container. -/
def densityInside {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι) (K : ConvexBody Space) : ℝ≥0∞ :=
  massInside F active K / volume (K : Set Space)

theorem indicesInside_mono {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) {s t : Finset ι} (hst : s ⊆ t)
    (K : ConvexBody Space) :
    indicesInside F s K ⊆ indicesInside F t K := by
  classical
  intro i hi
  rw [mem_indicesInside] at hi ⊢
  exact ⟨hst hi.1, hi.2⟩

theorem massInside_mono {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) {s t : Finset ι} (hst : s ⊆ t)
    (K : ConvexBody Space) :
    massInside F s K ≤ massInside F t K := by
  classical
  unfold massInside
  exact Finset.sum_le_sum_of_subset (indicesInside_mono F hst K)

theorem densityInside_mono {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) {s t : Finset ι} (hst : s ⊆ t)
    (K : ConvexBody Space) :
    densityInside F s K ≤ densityInside F t K := by
  exact ENNReal.div_le_div_right (massInside_mono F hst K) _

theorem massInside_eq_zero_of_indicesInside_eq_empty
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι) (active : Finset ι)
    (K : ConvexBody Space) (h : indicesInside F active K = ∅) :
    massInside F active K = 0 := by
  simp [massInside, h]

theorem densityInside_eq_zero_of_indicesInside_eq_empty
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι) (active : Finset ι)
    (K : ConvexBody Space) (h : indicesInside F active K = ∅) :
    densityInside F active K = 0 := by
  simp [densityInside, massInside, h]

theorem massInside_eq_zero_of_volume_eq_zero
    {ι : Type*} [Fintype ι] (F : ConvexFamily ι) (active : Finset ι)
    (K : ConvexBody Space) (hK : volume (K : Set Space) = 0) :
    massInside F active K = 0 := by
  classical
  unfold massInside
  apply Finset.sum_eq_zero
  intro i hi
  have hiK : (F i : Set Space) ⊆ (K : Set Space) :=
    (mem_indicesInside F active K i).1 hi |>.2
  exact bot_unique (by simpa [hK] using measure_mono (μ := volume) hiK)

/-- A maximizer of active density among an explicitly finite candidate set. -/
structure MaximalDensityChoice {ι κ : Type*} [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι) (candidates : Finset κ)
    (container : κ → ConvexBody Space) where
  index : κ
  index_mem : index ∈ candidates
  maximal : ∀ k ∈ candidates,
    densityInside F active (container k) ≤
      densityInside F active (container index)

namespace MaximalDensityChoice

variable {ι κ : Type*} [Fintype ι]
  {F : ConvexFamily ι} {active : Finset ι} {candidates : Finset κ}
  {container : κ → ConvexBody Space}

/-- The fiber extracted by the maximizing candidate. -/
def fiber (M : MaximalDensityChoice F active candidates container) : Finset ι :=
  indicesInside F active (container M.index)

theorem fiber_subset (M : MaximalDensityChoice F active candidates container) :
    M.fiber ⊆ active :=
  indicesInside_subset F active (container M.index)

theorem body_subset_container
    (M : MaximalDensityChoice F active candidates container)
    {i : ι} (hi : i ∈ M.fiber) :
    (F i : Set Space) ⊆ (container M.index : Set Space) :=
  (mem_indicesInside F active (container M.index) i).1 hi |>.2

/-- Restricting to the winning fiber cannot make it more concentrated in any
other candidate than the winning density at this greedy stage. -/
theorem fiber_density_le
    (M : MaximalDensityChoice F active candidates container)
    {k : κ} (hk : k ∈ candidates) :
    densityInside F M.fiber (container k) ≤
      densityInside F active (container M.index) :=
  (densityInside_mono F M.fiber_subset (container k)).trans (M.maximal k hk)

/-- Cross-multiplied finite-candidate Frostman inequality for the winning
fiber.  The zero-volume case is proved separately rather than cancelled. -/
theorem fiber_massInside_le
    (M : MaximalDensityChoice F active candidates container)
    {k : κ} (hk : k ∈ candidates) :
    massInside F M.fiber (container k) ≤
      densityInside F active (container M.index) *
        volume (container k : Set Space) := by
  let rho := densityInside F active (container M.index)
  by_cases hzero : volume (container k : Set Space) = 0
  · rw [massInside_eq_zero_of_volume_eq_zero F M.fiber (container k) hzero,
      hzero, mul_zero]
  · exact (ENNReal.div_le_iff_le_mul
      (Or.inl hzero)
      (Or.inl (container k).isCompact.measure_lt_top.ne)).1 (M.fiber_density_le hk)

end MaximalDensityChoice

/-- A finite candidate set always has a density maximizer. -/
theorem exists_maximalDensityChoice
    {ι κ : Type*} [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι)
    (candidates : Finset κ) (container : κ → ConvexBody Space)
    (hcandidates : candidates.Nonempty) :
    Nonempty (MaximalDensityChoice F active candidates container) := by
  classical
  obtain ⟨k, hk, hmax⟩ :=
    Finset.exists_max_image candidates (fun j ↦ densityInside F active (container j))
      hcandidates
  exact ⟨{
    index := k
    index_mem := hk
    maximal := fun j hj ↦ hmax j hj
  }⟩

/-- Under finite candidate coverage, a maximizer can be chosen with a nonempty
fiber.  This tie-handles zero-volume bodies by maximizing only among the
nonempty fibers and observing that every empty fiber has density zero. -/
theorem exists_maximalDensityChoice_fiber_nonempty
    {ι κ : Type*} [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι)
    (candidates : Finset κ) (container : κ → ConvexBody Space)
    (hactive : active.Nonempty)
    (hcover : ∀ i ∈ active, ∃ k ∈ candidates,
      (F i : Set Space) ⊆ (container k : Set Space)) :
    ∃ M : MaximalDensityChoice F active candidates container,
      M.fiber.Nonempty := by
  classical
  let eligible := candidates.filter fun k ↦ (indicesInside F active (container k)).Nonempty
  have heligible : eligible.Nonempty := by
    obtain ⟨i, hi⟩ := hactive
    obtain ⟨k, hk, hik⟩ := hcover i hi
    refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩⟩
    exact ⟨i, (mem_indicesInside F active (container k) i).2 ⟨hi, hik⟩⟩
  obtain ⟨k, hkEligible, hmax⟩ :=
    Finset.exists_max_image eligible (fun j ↦ densityInside F active (container j))
      heligible
  have hk := (Finset.mem_filter.mp hkEligible).1
  have hkFiber := (Finset.mem_filter.mp hkEligible).2
  let M : MaximalDensityChoice F active candidates container :=
    { index := k
      index_mem := hk
      maximal := fun j hj ↦ by
        by_cases hjFiber : (indicesInside F active (container j)).Nonempty
        · exact hmax j (Finset.mem_filter.mpr ⟨hj, hjFiber⟩)
        · have hempty : indicesInside F active (container j) = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hjFiber
          rw [densityInside_eq_zero_of_indicesInside_eq_empty F active (container j) hempty]
          exact bot_le }
  exact ⟨M, hkFiber⟩

/-- A terminating greedy decomposition.  Every step stores an actual finite
candidate maximizer and removes its nonempty fiber before recursing. -/
inductive GreedyDensityPartition {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (candidates : Finset κ)
    (container : κ → ConvexBody Space) : Finset ι → Type _
  | empty : GreedyDensityPartition F candidates container ∅
  | step {active : Finset ι}
      (choice : MaximalDensityChoice F active candidates container)
      (fiber_nonempty : choice.fiber.Nonempty)
      (tail : GreedyDensityPartition F candidates container (active \ choice.fiber)) :
      GreedyDensityPartition F candidates container active

namespace GreedyDensityPartition

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  {F : ConvexFamily ι} {candidates : Finset κ}
  {container : κ → ConvexBody Space} {active : Finset ι}

/-- The union of all fibers stored in the greedy decomposition. -/
def coveredIndices : {s : Finset ι} →
    GreedyDensityPartition F candidates container s → Finset ι
  | _, .empty => ∅
  | _, .step choice _ tail => choice.fiber ∪ tail.coveredIndices

/-- The recursive greedy fibers cover the original active index set exactly. -/
theorem coveredIndices_eq (P : GreedyDensityPartition F candidates container active) :
    P.coveredIndices = active := by
  induction P with
  | empty => rfl
  | @step current choice hnonempty tail ih =>
      simp only [coveredIndices, ih]
      exact Finset.union_sdiff_of_subset choice.fiber_subset

/-- Number of extraction steps in the terminating greedy certificate. -/
def length : {s : Finset ι} →
    GreedyDensityPartition F candidates container s → Nat
  | _, .empty => 0
  | _, .step _ _ tail => tail.length + 1

/-- At most one nonempty fiber can be extracted per original active index. -/
theorem length_le_card (P : GreedyDensityPartition F candidates container active) :
    P.length ≤ active.card := by
  induction P with
  | empty => simp [length]
  | @step current choice hnonempty tail ih =>
      have hproper : current \ choice.fiber ⊂ current :=
        Finset.sdiff_ssubset choice.fiber_subset hnonempty
      have hlt : (current \ choice.fiber).card < current.card :=
        Finset.card_lt_card hproper
      simpa [length, Nat.add_comm] using Nat.succ_le_of_lt (ih.trans_lt hlt)

end GreedyDensityPartition

/-- Finite coverage produces a terminating greedy maximal-density partition. -/
theorem exists_greedyDensityPartition
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (active : Finset ι)
    (candidates : Finset κ) (container : κ → ConvexBody Space)
    (hcover : ∀ i ∈ active, ∃ k ∈ candidates,
      (F i : Set Space) ⊆ (container k : Set Space)) :
    Nonempty (GreedyDensityPartition F candidates container active) := by
  classical
  refine Finset.strongInductionOn active ?_ hcover
  intro current ih hcurrentCover
  by_cases hempty : current = ∅
  · subst current
    exact ⟨GreedyDensityPartition.empty⟩
  · have hcurrent : current.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨choice, hfiber⟩ :=
      exists_maximalDensityChoice_fiber_nonempty F current candidates container
        hcurrent hcurrentCover
    have hproper : current \ choice.fiber ⊂ current :=
      Finset.sdiff_ssubset choice.fiber_subset hfiber
    have hcover' : ∀ i ∈ current \ choice.fiber, ∃ k ∈ candidates,
        (F i : Set Space) ⊆ (container k : Set Space) := by
      intro i hi
      exact hcurrentCover i (Finset.mem_sdiff.mp hi).1
    obtain ⟨tail⟩ := ih (current \ choice.fiber) hproper hcover'
    exact ⟨GreedyDensityPartition.step choice hfiber tail⟩

end

end Submission.Kakeya.ConvexFactoring
