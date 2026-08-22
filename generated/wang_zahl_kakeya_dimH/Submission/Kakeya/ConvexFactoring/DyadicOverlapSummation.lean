import Submission.Kakeya.ConvexFactoring.PairwiseOverlap

/-!
# Dyadic overlap row summation

This file isolates the finite combinatorial summation layer needed after a
geometric pairwise-overlap estimate has assigned every ordered pair to a
dyadic level. The hypotheses deliberately expose all geometric inputs:

* a pairwise overlap bound at the assigned level;
* containment of the second body in the row/level container;
* a Katz--Tao nonconcentration bound for the body family; and
* the comparison between scale times container volume and the row shading.

No final row estimate is packaged as input.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]
variable {F : ConvexFamily ι} {Y : Shading F}

/-- The indices in row `i` assigned to dyadic level `k`. -/
def dyadicOverlapBucket (level : ι → ι → κ) (i : ι) (k : κ) : Finset ι :=
  Finset.univ.filter fun j => level i j = k

/-- The geometric majorant attached to an ordered pair. -/
def dyadicOverlapMajorant
    (level : ι → ι → κ) (q : ι → κ → ENNReal) (i j : ι) : ENNReal :=
  q i (level i j) * volume (F j : Set Space)

/-- The contribution of one dyadic bucket is bounded using containment and
Katz--Tao nonconcentration, followed by the scale/container comparison. -/
theorem dyadicOverlapBucket_majorant_le
    (levels : Finset κ)
    (level : ι → ι → κ)
    (container : ι → κ → ConvexBody Space)
    (q : ι → κ → ENNReal)
    (C A : ENNReal)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao C F)
    (hscale : ∀ i k, k ∈ levels →
      q i k * volume (container i k : Set Space) ≤ A * volume (Y.carrier i))
    (i : ι) (k : κ) (hk : k ∈ levels) :
    (∑ j ∈ dyadicOverlapBucket level i k,
        dyadicOverlapMajorant (F := F) level q i j) ≤
      (C * A) * volume (Y.carrier i) := by
  classical
  have hbodyMass :
      (∑ j ∈ dyadicOverlapBucket level i k, volume (F j : Set Space)) ≤
        containedMass F (container i k) := by
    unfold containedMass
    apply Finset.sum_le_sum_of_subset
    intro j hj
    rw [mem_containedIndices]
    have hjk : level i j = k := (Finset.mem_filter.mp hj).2
    simpa [hjk] using hcontained i j
  have hKT' :
      containedMass F (container i k) ≤ C * volume (container i k : Set Space) := by
    simpa [IsKatzTaoAt] using hKT (container i k)
  calc
    (∑ j ∈ dyadicOverlapBucket level i k,
        dyadicOverlapMajorant (F := F) level q i j) =
        q i k * (∑ j ∈ dyadicOverlapBucket level i k,
          volume (F j : Set Space)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : level i j = k := (Finset.mem_filter.mp hj).2
      simp [dyadicOverlapMajorant, hjk]
    _ ≤ q i k * containedMass F (container i k) := by
      gcongr
    _ ≤ q i k * (C * volume (container i k : Set Space)) := by
      gcongr
    _ = C * (q i k * volume (container i k : Set Space)) := by
      ac_rfl
    _ ≤ C * (A * volume (Y.carrier i)) :=
      mul_le_mul_right (hscale i k hk) C
    _ = (C * A) * volume (Y.carrier i) := by
      ac_rfl

/-- Summing the bucket estimates with `Finset.sum_fiberwise_of_maps_to`
gives the dyadic majorant row bound. -/
theorem dyadicOverlapMajorant_row_le
    (levels : Finset κ)
    (level : ι → ι → κ)
    (container : ι → κ → ConvexBody Space)
    (q : ι → κ → ENNReal)
    (C A : ENNReal)
    (hlevel : ∀ i j, level i j ∈ levels)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao C F)
    (hscale : ∀ i k, k ∈ levels →
      q i k * volume (container i k : Set Space) ≤ A * volume (Y.carrier i))
    (i : ι) :
    (∑ j, dyadicOverlapMajorant (F := F) level q i j) ≤
      ((levels.card : ENNReal) * C * A) * volume (Y.carrier i) := by
  classical
  have hsplit :
      (∑ j, dyadicOverlapMajorant (F := F) level q i j) =
        ∑ k ∈ levels, ∑ j ∈ dyadicOverlapBucket level i k,
          dyadicOverlapMajorant (F := F) level q i j := by
    simpa [dyadicOverlapBucket] using
      (Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := levels) (g := level i)
        (fun j _ => hlevel i j)
        (fun j => dyadicOverlapMajorant (F := F) level q i j)).symm
  rw [hsplit]
  calc
    (∑ k ∈ levels, ∑ j ∈ dyadicOverlapBucket level i k,
        dyadicOverlapMajorant (F := F) level q i j) ≤
        ∑ k ∈ levels, (C * A) * volume (Y.carrier i) := by
      apply Finset.sum_le_sum
      intro k hk
      exact dyadicOverlapBucket_majorant_le levels level container q C A
        hcontained hKT hscale i k hk
    _ = ((levels.card : ENNReal) * C * A) * volume (Y.carrier i) := by
      simp
      ac_rfl

/-- The actual overlap row is bounded by the same dyadic factor. In
particular, the pairwise geometric hypothesis remains explicit rather than
being replaced by an assumed row estimate. -/
theorem dyadicOverlap_row_le
    (levels : Finset κ)
    (level : ι → ι → κ)
    (container : ι → κ → ConvexBody Space)
    (q : ι → κ → ENNReal)
    (C A : ENNReal)
    (hlevel : ∀ i j, level i j ∈ levels)
    (hpairwise : ∀ i j,
      volume (Y.carrier i ∩ Y.carrier j) ≤
        q i (level i j) * volume (F j : Set Space))
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao C F)
    (hscale : ∀ i k, k ∈ levels →
      q i k * volume (container i k : Set Space) ≤ A * volume (Y.carrier i))
    (i : ι) :
    (∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      ((levels.card : ENNReal) * C * A) * volume (Y.carrier i) := by
  calc
    (∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
        ∑ j, dyadicOverlapMajorant (F := F) level q i j := by
      exact Finset.sum_le_sum fun j _ => hpairwise i j
    _ ≤ ((levels.card : ENNReal) * C * A) * volume (Y.carrier i) :=
      dyadicOverlapMajorant_row_le levels level container q C A
        hlevel hcontained hKT hscale i

/-- Package the pairwise geometric estimates as the released overlap-bound
interface. -/
def dyadicPairwiseOverlapBound
    (level : ι → ι → κ)
    (q : ι → κ → ENNReal)
    (hpairwise : ∀ i j,
      volume (Y.carrier i ∩ Y.carrier j) ≤
        q i (level i j) * volume (F j : Set Space)) :
    PairwiseOverlapBound Y where
  majorant := dyadicOverlapMajorant (F := F) level q
  pairwise_le := hpairwise

/-- The dyadic row summation feeds directly into the released second-moment
interface. -/
theorem dyadicOverlap_secondMoment_le
    (levels : Finset κ)
    (level : ι → ι → κ)
    (container : ι → κ → ConvexBody Space)
    (q : ι → κ → ENNReal)
    (C A : ENNReal)
    (hlevel : ∀ i j, level i j ∈ levels)
    (hpairwise : ∀ i j,
      volume (Y.carrier i ∩ Y.carrier j) ≤
        q i (level i j) * volume (F j : Set Space))
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao C F)
    (hscale : ∀ i k, k ∈ levels →
      q i k * volume (container i k : Set Space) ≤ A * volume (Y.carrier i)) :
    (∫⁻ x, (Y.pointMultiplicity x : ENNReal) ^ 2 ∂volume) ≤
      ((levels.card : ENNReal) * C * A) * Y.shadingMass := by
  let B : PairwiseOverlapBound Y :=
    dyadicPairwiseOverlapBound level q hpairwise
  apply B.secondMoment_le_factor_mul_shadingMass_of_row_le
  intro i
  exact dyadicOverlapMajorant_row_le levels level container q C A
    hlevel hcontained hKT hscale i

/-- Córdoba's inequality converts the dyadic row bound into a lower bound for
the union, in multiplication form. -/
theorem shadingMass_le_dyadicFactor_mul_volume_shadedUnion
    (levels : Finset κ)
    (level : ι → ι → κ)
    (container : ι → κ → ConvexBody Space)
    (q : ι → κ → ENNReal)
    (C A : ENNReal)
    (hlevel : ∀ i j, level i j ∈ levels)
    (hpairwise : ∀ i j,
      volume (Y.carrier i ∩ Y.carrier j) ≤
        q i (level i j) * volume (F j : Set Space))
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao C F)
    (hscale : ∀ i k, k ∈ levels →
      q i k * volume (container i k : Set Space) ≤ A * volume (Y.carrier i)) :
    Y.shadingMass ≤
      ((levels.card : ENNReal) * C * A) * volume Y.shadedUnion := by
  let B : PairwiseOverlapBound Y :=
    dyadicPairwiseOverlapBound level q hpairwise
  apply B.shadingMass_le_factor_mul_volume_shadedUnion_of_row_le
  intro i
  exact dyadicOverlapMajorant_row_le levels level container q C A
    hlevel hcontained hKT hscale i

/-- The division form of the same union lower bound. -/
theorem shadingMass_div_dyadicFactor_le_volume_shadedUnion
    (levels : Finset κ)
    (level : ι → ι → κ)
    (container : ι → κ → ConvexBody Space)
    (q : ι → κ → ENNReal)
    (C A : ENNReal)
    (hlevel : ∀ i j, level i j ∈ levels)
    (hpairwise : ∀ i j,
      volume (Y.carrier i ∩ Y.carrier j) ≤
        q i (level i j) * volume (F j : Set Space))
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao C F)
    (hscale : ∀ i k, k ∈ levels →
      q i k * volume (container i k : Set Space) ≤ A * volume (Y.carrier i)) :
    Y.shadingMass / ((levels.card : ENNReal) * C * A) ≤
      volume Y.shadedUnion := by
  let B : PairwiseOverlapBound Y :=
    dyadicPairwiseOverlapBound level q hpairwise
  apply B.shadingMass_div_factor_le_volume_shadedUnion_of_row_le
  intro i
  exact dyadicOverlapMajorant_row_le levels level container q C A
    hlevel hcontained hKT hscale i

end

end Submission.Kakeya.ConvexFactoring
