import Family8Grounding.Family8StickyMassPopularRelativeScaleCoefficientV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped ENNReal NNReal

namespace Family8CardWeightedActiveParentCardScaleCancellationV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyMassPopularRelativeScaleCoefficientV1

noncomputable section

/-!
# Exact cancellation of the remaining active-parent count

After card-weighted mass popularity, Equation (46) contains one copy of the
number of active parents.  This copy should not be bounded separately: the
identity

`|T_rho| * delta^2 = (|T_rho| * rho^2) * (delta / rho)^2`

matches the relative square already present on the right.  The theorem below
performs precisely that division-free cancellation.  Its only geometric
input is an upper bound for the genuine normalized parent mass.

V1 was a failed ASCII-notation draft and is deliberately not imported.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem cardWeighted_activeCoarse_le_relativeSquare_of_cardScaleMass
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    {prefactor loss KT X rhs : ENNReal}
    (hX : (activeCoarseCardScaleMass S : ENNReal) ≤ X)
    (hscaled :
      prefactor * (loss * X * KT) ≤
        (delta : ENNReal) ^ 2 * rhs) :
    prefactor *
        (loss * (S.activeCoarse.card : ENNReal) * KT) ≤
      (((delta : ENNReal) / (rho : ENNReal)) ^ 2) * rhs := by
  have hdSq0 : (delta : ENNReal) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne')
  have hdSqTop : (delta : ENNReal) ^ 2 ≠ ∞ := by
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hidentity :=
    activeCoarse_card_mul_delta_sq_eq_cardScaleMass_mul_ratio_sq S hrho
  apply (ENNReal.mul_le_mul_iff_left hdSq0 hdSqTop).mp
  calc
    (prefactor *
          (loss * (S.activeCoarse.card : ENNReal) * KT)) *
          (delta : ENNReal) ^ 2 =
        (prefactor * (loss * KT)) *
          ((S.activeCoarse.card : ENNReal) *
            (delta : ENNReal) ^ 2) := by ring
    _ = (prefactor * (loss * KT)) *
          ((activeCoarseCardScaleMass S : ENNReal) *
            (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) := by
      rw [hidentity]
    _ ≤ (prefactor * (loss * KT)) *
          (X * (((delta : ENNReal) / (rho : ENNReal)) ^ 2)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' hX le_rfl)
    _ = (prefactor * (loss * X * KT)) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2) := by ring
    _ ≤ ((delta : ENNReal) ^ 2 * rhs) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2) := by
      exact mul_le_mul' hscaled le_rfl
    _ = ((((delta : ENNReal) / (rho : ENNReal)) ^ 2) * rhs) *
          (delta : ENNReal) ^ 2 := by ring

#print axioms
  cardWeighted_activeCoarse_le_relativeSquare_of_cardScaleMass

end
end Family8CardWeightedActiveParentCardScaleCancellationV2
