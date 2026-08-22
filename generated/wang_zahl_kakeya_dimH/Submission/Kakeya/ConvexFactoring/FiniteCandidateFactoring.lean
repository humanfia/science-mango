import Submission.Kakeya.ConvexFactoring.MaximalDensity
import Submission.Kakeya.ConvexFactoring.NonConcentration
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

namespace MaximalDensityChoice

variable {ι κ : Type*} [Fintype ι]
  {F : ConvexFamily ι} {active : Finset ι} {candidates : Finset κ}
  {container : κ → ConvexBody Space}

/-- The mass captured by the winner is exactly the mass of its extracted
fiber inside the winning container. -/
theorem fiber_massInside_self_eq
    (M : MaximalDensityChoice F active candidates container) :
    massInside F M.fiber (container M.index) =
      massInside F active (container M.index) := by
  classical
  have hindices : indicesInside F M.fiber (container M.index) = M.fiber := by
    ext i
    rw [mem_indicesInside]
    constructor
    · exact fun hi ↦ hi.1
    · intro hi
      exact ⟨hi, M.body_subset_container hi⟩
  unfold massInside
  rw [hindices]
  rfl

/-- The winning fiber obeys the finite-candidate Frostman inequality with
denominators cleared. This remains valid for zero-volume containers. -/
theorem fiber_frostmanCross_le
    (M : MaximalDensityChoice F active candidates container)
    {k : κ} (hk : k ∈ candidates) :
    massInside F M.fiber (container k) *
        volume (container M.index : Set Space) ≤
      massInside F M.fiber (container M.index) *
        volume (container k : Set Space) := by
  rw [M.fiber_massInside_self_eq]
  by_cases hwin : volume (container M.index : Set Space) = 0
  · simp [hwin]
  · calc
      massInside F M.fiber (container k) *
          volume (container M.index : Set Space) ≤
          (densityInside F active (container M.index) *
            volume (container k : Set Space)) *
              volume (container M.index : Set Space) := by
            gcongr
            exact M.fiber_massInside_le hk
      _ = (densityInside F active (container M.index) *
            volume (container M.index : Set Space)) *
              volume (container k : Set Space) := by
            ac_rfl
      _ = massInside F active (container M.index) *
              volume (container k : Set Space) := by
            rw [densityInside, ENNReal.div_mul_cancel hwin
              (container M.index).isCompact.measure_lt_top.ne]

end MaximalDensityChoice

namespace GreedyDensityPartition

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  {F : ConvexFamily ι} {candidates : Finset κ}
  {container : κ → ConvexBody Space} {active : Finset ι}

/-- Every actual greedy step carries the cross-multiplied Frostman bound for
its actual winning fiber against every finite candidate. -/
def AllWinnerCross : {s : Finset ι} →
    GreedyDensityPartition F candidates container s → Prop
  | _, .empty => True
  | _, .step choice _ tail =>
      (∀ k ∈ candidates,
        massInside F choice.fiber (container k) *
            volume (container choice.index : Set Space) ≤
          massInside F choice.fiber (container choice.index) *
            volume (container k : Set Space)) ∧
      AllWinnerCross tail

/-- The recursive greedy construction automatically satisfies all winner
cross bounds; no separate certificate is assumed. -/
theorem allWinnerCross
    (P : GreedyDensityPartition F candidates container active) :
    AllWinnerCross P := by
  induction P with
  | empty => trivial
  | step choice fiber_nonempty tail ih =>
      exact ⟨fun k hk ↦ choice.fiber_frostmanCross_le hk, ih⟩

/-- Sum of an arbitrary nonnegative weight over the actual extracted fibers. -/
def extractedWeight (w : ι → ℝ≥0∞) : {s : Finset ι} →
    GreedyDensityPartition F candidates container s → ℝ≥0∞
  | _, .empty => 0
  | _, .step choice _ tail =>
      (∑ i ∈ choice.fiber, w i) + extractedWeight w tail

/-- Greedy extraction loses no weight: the disjoint recursive fibers sum
exactly to the original active weight. -/
theorem extractedWeight_eq
    (P : GreedyDensityPartition F candidates container active)
    (w : ι → ℝ≥0∞) :
    extractedWeight w P = ∑ i ∈ active, w i := by
  induction P with
  | empty => simp [extractedWeight]
  | step choice fiber_nonempty tail ih =>
      simp only [extractedWeight, ih]
      simpa [add_comm] using
        (Finset.sum_sdiff (f := w) choice.fiber_subset)

/-- In the quantitative-refinement language, the complete greedy partition
retains the active body mass with loss exactly one. -/
theorem bodyMass_withinFactor_one
    (P : GreedyDensityPartition F candidates container active) :
    WithinFactor 1 (∑ i ∈ active, volume (F i : Set Space))
      (extractedWeight (fun i ↦ volume (F i : Set Space)) P) := by
  unfold WithinFactor
  rw [P.extractedWeight_eq]
  simp

end GreedyDensityPartition

/-- Concrete finite-candidate factoring existence: an actual terminating
greedy partition, exact index coverage, per-step winner Frostman bounds, an
explicit step bound, and loss-one active body mass retention. -/
theorem exists_finiteCandidateGreedyFactoring
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (active : Finset ι)
    (candidates : Finset κ) (container : κ → ConvexBody Space)
    (hcover : ∀ i ∈ active, ∃ k ∈ candidates,
      (F i : Set Space) ⊆ (container k : Set Space)) :
    ∃ P : GreedyDensityPartition F candidates container active,
      P.coveredIndices = active ∧
      P.length ≤ active.card ∧
      P.AllWinnerCross ∧
      P.extractedWeight (fun i ↦ volume (F i : Set Space)) =
        ∑ i ∈ active, volume (F i : Set Space) ∧
      WithinFactor 1 (∑ i ∈ active, volume (F i : Set Space))
        (P.extractedWeight (fun i ↦ volume (F i : Set Space))) := by
  classical
  obtain ⟨P⟩ := exists_greedyDensityPartition F active candidates container hcover
  exact ⟨P, P.coveredIndices_eq, P.length_le_card, P.allWinnerCross,
    P.extractedWeight_eq _, P.bodyMass_withinFactor_one⟩

end

end Submission.Kakeya.ConvexFactoring
