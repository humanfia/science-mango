import Submission.Kakeya.ConvexFactoring.FrameBoxThickening
import Submission.Kakeya.ConvexFactoring.NeighborhoodInducedShading

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

namespace ConvexFactorization

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- A neighborhood-induced carrier is contained in the metric thickening
before the additional intersection with its coarse body. -/
theorem neighborhoodInducedShading_subset_thickening
    (P : ConvexFactorization F W) (Y : Shading F)
    (r : ℝ) (k : κ) :
    (P.neighborhoodInducedShading Y r).carrier k ⊆
      Metric.thickening r (P.fiberShadedUnion Y k) :=
  Set.inter_subset_right

/-- If one fiber's shaded union lies in a frame box, the corresponding
neighborhood-induced carrier obeys the explicit widened-box volume bound. -/
theorem volume_neighborhoodInducedShading_carrier_le_box
    (P : ConvexFactorization F W) (Y : Shading F)
    (B : FrameBox) (k : κ)
    (hfiber : P.fiberShadedUnion Y k ⊆ B.carrier) (r : ℝ≥0) :
    volume ((P.neighborhoodInducedShading Y (r : ℝ)).carrier k) ≤
      ∏ i, ((B.side i : ℝ≥0∞) + 2 * (r : ℝ≥0∞)) := by
  exact (measure_mono (P.neighborhoodInducedShading_subset_thickening
      Y (r : ℝ) k)).trans
    (B.volume_thickening_le_prod_side_add_two_mul
      (P.fiberShadedUnion Y k) hfiber r)

/-- It is enough for the coarse body itself to lie in the chosen frame box. -/
theorem volume_neighborhoodInducedShading_carrier_le_box_of_coarseBody
    (P : ConvexFactorization F W) (Y : Shading F)
    (B : FrameBox) (k : κ)
    (hcoarse : (W k : Set Space) ⊆ B.carrier) (r : ℝ≥0) :
    volume ((P.neighborhoodInducedShading Y (r : ℝ)).carrier k) ≤
      ∏ i, ((B.side i : ℝ≥0∞) + 2 * (r : ℝ≥0∞)) := by
  apply P.volume_neighborhoodInducedShading_carrier_le_box Y B k
  exact (P.fiberShadedUnion_subset_coarseBody Y k).trans hcoarse

/-- Summing the preceding geometric estimate gives an explicit total-mass
bound for the neighborhood-induced coarse shading. -/
theorem neighborhoodInducedShading_mass_le_sum_boxBounds
    [Fintype κ] (P : ConvexFactorization F W) (Y : Shading F)
    (box : κ → FrameBox)
    (hcoarse : ∀ k, (W k : Set Space) ⊆ (box k).carrier) (r : ℝ≥0) :
    (P.neighborhoodInducedShading Y (r : ℝ)).shadingMass ≤
      ∑ k, ∏ i, (((box k).side i : ℝ≥0∞) + 2 * (r : ℝ≥0∞)) := by
  unfold Shading.shadingMass
  exact Finset.sum_le_sum fun k _ ↦
    P.volume_neighborhoodInducedShading_carrier_le_box_of_coarseBody
      Y (box k) k (hcoarse k) r

end ConvexFactorization

end

end Submission.Kakeya.ConvexFactoring
