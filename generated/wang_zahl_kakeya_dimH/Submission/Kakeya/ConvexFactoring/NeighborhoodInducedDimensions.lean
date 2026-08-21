import Submission.Kakeya.ConvexFactoring.NeighborhoodInducedVolume

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Certified dimensions for neighborhood-induced shadings

This module extracts the actual outer frame box stored by a
`HasBoxDimensions` certificate and applies the widened-box estimate to the
paper-style neighborhood-induced shading.  No John-ellipsoid existence is
asserted here: the certificate remains an explicit mathematical input.
-/

namespace ConvexFactorization

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- A box-dimensions certificate supplies an actual outer frame box for the
neighborhood-induced carrier and hence the widened-box volume estimate. -/
theorem exists_frameBox_volume_neighborhoodInducedShading_carrier_le
    (P : ConvexFactorization F W) (Y : Shading F)
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} (k : κ)
    (hdim : HasBoxDimensions C side (W k)) (r : ℝ≥0) :
    ∃ B : FrameBox,
      B.side = side ∧
      volume ((P.neighborhoodInducedShading Y (r : ℝ)).carrier k) ≤
        ∏ i, ((side i : ℝ≥0∞) + 2 * (r : ℝ≥0∞)) := by
  obtain ⟨_hC, B, hside, _hinner, houter⟩ := hdim
  refine ⟨B, hside, ?_⟩
  have hcoarse : (W k : Set Space) ⊆ B.carrier := by
    intro x hx
    exact houter hx
  simpa only [hside] using
    P.volume_neighborhoodInducedShading_carrier_le_box_of_coarseBody
      Y B k hcoarse r

/-- If all coarse bodies have one certified dimension pattern, summing their
actual outer-box bounds costs only the cardinality of the coarse index type. -/
theorem neighborhoodInducedShading_mass_le_card_mul_of_hasBoxDimensions
    [Fintype κ] (P : ConvexFactorization F W) (Y : Shading F)
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0}
    (hdim : ∀ k, HasBoxDimensions C side (W k)) (r : ℝ≥0) :
    (P.neighborhoodInducedShading Y (r : ℝ)).shadingMass ≤
      (Fintype.card κ : ℝ≥0∞) *
        ∏ i, ((side i : ℝ≥0∞) + 2 * (r : ℝ≥0∞)) := by
  let Q : ℝ≥0∞ := ∏ i, ((side i : ℝ≥0∞) + 2 * (r : ℝ≥0∞))
  unfold Shading.shadingMass
  calc
    ∑ k, volume ((P.neighborhoodInducedShading Y (r : ℝ)).carrier k) ≤
        ∑ _k : κ, Q := by
          apply Finset.sum_le_sum
          intro k _hk
          obtain ⟨B, _hside, hB⟩ :=
            P.exists_frameBox_volume_neighborhoodInducedShading_carrier_le
              Y k (hdim k) r
          exact hB
    _ = (Fintype.card κ : ℝ≥0∞) * Q := by
          simp [nsmul_eq_mul]

end ConvexFactorization

end

end Submission.Kakeya.ConvexFactoring
