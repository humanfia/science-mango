import Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FullConvexMaximalDensity
open GreedyOccurrenceFactorization
open GreedyDensityBucketing

namespace GreedyDensityCoverCost

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable {F : ConvexFamily ι} {candidates : Finset κ}
  {container : κ → ConvexBody Space} {active : Finset ι}

/-- Selected disjoint greedy blocks never carry more mass than the original
active family. -/
theorem sum_blockMass_le_activeMass
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length)) :
    (∑ k ∈ S, blockMass F (blockAt F P k)) ≤
      ∑ i ∈ active, volume (F i : Set Space) := by
  classical
  have hdisj := blockAt_fibers_pairwiseDisjoint F P S
  have hsubset : S.biUnion (fun k => (blockAt F P k).fiber) ⊆ active := by
    intro i hi
    obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hi
    exact blockAt_fiber_subset_active F P k hik
  calc
    (∑ k ∈ S, blockMass F (blockAt F P k)) =
        ∑ k ∈ S, ∑ i ∈ (blockAt F P k).fiber,
          volume (F i : Set Space) := by rfl
    _ = ∑ i ∈ S.biUnion (fun k => (blockAt F P k).fiber),
        volume (F i : Set Space) := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ i ∈ active, volume (F i : Set Space) :=
      Finset.sum_le_sum_of_subset hsubset

/-- All greedy occurrence blocks decompose the active body mass exactly. -/
theorem sum_blockMass_univ_eq_activeMass
    (P : GreedyDensityPartition F candidates container active) :
    (∑ k : Fin (blocks F P).length, blockMass F (blockAt F P k)) =
      ∑ i ∈ active, volume (F i : Set Space) := by
  classical
  have hdisj := blockAt_fibers_pairwiseDisjoint F P
    (Finset.univ : Finset (Fin (blocks F P).length))
  calc
    (∑ k : Fin (blocks F P).length, blockMass F (blockAt F P k)) =
        ∑ k : Fin (blocks F P).length,
          ∑ i ∈ (blockAt F P k).fiber,
            volume (F i : Set Space) := by rfl
    _ = ∑ i ∈ Finset.univ.biUnion (fun k => (blockAt F P k).fiber),
        volume (F i : Set Space) := (Finset.sum_biUnion hdisj).symm
    _ = ∑ i ∈ active, volume (F i : Set Space) := by
      rw [biUnion_blockAt_eq_active F P]

/-- A common positive density lower bound on selected occurrence blocks
directly yields an aggregate cover cost. No per-parent lots or cost input is
assumed. -/
theorem densityLower_coverCost
    (P : GreedyDensityPartition F candidates container active)
    (S : Finset (Fin (blocks F P).length))
    (d A : ℝ≥0∞) (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hlower : ∀ k ∈ S, d ≤ blockDensity F (blockAt F P k)) :
    A * (∑ k ∈ S, volume ((blockAt F P k).body : Set Space)) ≤
      (A / d) * (∑ i ∈ active, volume (F i : Set Space)) := by
  have hdensity : d *
      (∑ k ∈ S, volume ((blockAt F P k).body : Set Space)) ≤
      ∑ i ∈ active, volume (F i : Set Space) := by
    calc
      d * (∑ k ∈ S, volume ((blockAt F P k).body : Set Space)) =
          ∑ k ∈ S, d * volume ((blockAt F P k).body : Set Space) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ S, blockMass F (blockAt F P k) := by
        exact Finset.sum_le_sum fun k hk =>
          lower_mul_volume_le_blockMass F (blockAt F P k) d (hlower k hk)
      _ ≤ ∑ i ∈ active, volume (F i : Set Space) :=
        sum_blockMass_le_activeMass P S
  have hcross :
      (A * (∑ k ∈ S, volume ((blockAt F P k).body : Set Space))) * d ≤
        A * (∑ i ∈ active, volume (F i : Set Space)) := by
    calc
      (A * (∑ k ∈ S, volume ((blockAt F P k).body : Set Space))) * d =
          A * (d * ∑ k ∈ S,
            volume ((blockAt F P k).body : Set Space)) := by ac_rfl
      _ ≤ A * (∑ i ∈ active, volume (F i : Set Space)) :=
        mul_le_mul' le_rfl hdensity
  have hdiv :
      A * (∑ k ∈ S, volume ((blockAt F P k).body : Set Space)) ≤
        (A * (∑ i ∈ active, volume (F i : Set Space))) / d :=
    (ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdTop)).2 hcross
  calc
    A * (∑ k ∈ S, volume ((blockAt F P k).body : Set Space)) ≤
        (A * (∑ i ∈ active, volume (F i : Set Space))) / d := hdiv
    _ = (A / d) * (∑ i ∈ active, volume (F i : Set Space)) := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ac_rfl

/-- Balanced density bucketing replaces candidate-count loss by the finite
density-label count. The same selected bucket has a derived aggregate cover
cost at its certified bucket lower endpoint. -/
theorem exists_densityBucket_with_retention_and_coverCost
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (base : Finset ι)
    (P : GreedyDensityPartition F (hullCandidates base)
      (hullContainer F) active)
    (label : ℝ≥0∞ → β) (lower : β → ℝ≥0∞) (A : ℝ≥0∞)
    (hlower : ∀ x, lower (label x) ≤ x)
    (hlower0 : ∀ b, lower b ≠ 0)
    (hlowerTop : ∀ b, lower b ≠ ∞) :
    ∃ b : β,
      (∑ i ∈ active, volume (F i : Set Space)) ≤
        (Fintype.card β : ℝ≥0∞) *
          ∑ k ∈ occurrenceDensityBucket F base P label b,
            blockMass F (blockAt F P k) ∧
      A * (∑ k ∈ occurrenceDensityBucket F base P label b,
        volume ((blockAt F P k).body : Set Space)) ≤
        (A / lower b) *
          (∑ i ∈ active, volume (F i : Set Space)) := by
  obtain ⟨b, hb⟩ := exists_occurrenceDensityBucket_mass_loss
    F base P label
  refine ⟨b, ?_, densityLower_coverCost P
    (occurrenceDensityBucket F base P label b) (lower b) A
      (hlower0 b) (hlowerTop b) ?_⟩
  · rw [← sum_blockMass_univ_eq_activeMass P]
    exact hb
  · intro k hk
    have hkLabel := (mem_occurrenceDensityBucket F base P label b k).1 hk
    simpa [hkLabel] using hlower (blockDensity F (blockAt F P k))

end

end GreedyDensityCoverCost

end Submission.Kakeya.ConvexFactoring
