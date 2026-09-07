import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrozenCoarseB2CardScaleBaseBudgetV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

private theorem ennreal_card_eighth_sq_half
    (c r : ENNReal) :
    c * ((r / 8) ^ 2 / 2) = c * r ^ 2 / 128 := by
  have hconstant :
      (8 : ENNReal)⁻¹ * (8 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ =
        (128 : ENNReal)⁻¹ := by
    have hnn :
        (8 : NNReal)⁻¹ * (8 : NNReal)⁻¹ * (2 : NNReal)⁻¹ =
          (128 : NNReal)⁻¹ := by
      norm_num
    have hc := congrArg (fun x : NNReal => (x : ENNReal)) hnn
    rw [ENNReal.coe_mul, ENNReal.coe_mul,
      ENNReal.coe_inv (r := (2 : NNReal)) (by norm_num),
      ENNReal.coe_inv (r := (8 : NNReal)) (by norm_num),
      ENNReal.coe_inv (r := (128 : NNReal)) (by norm_num)] at hc
    norm_num at hc
    exact hc
  calc
    c * ((r / 8) ^ 2 / 2) =
        c * (r * r) * ((8 : ENNReal)⁻¹ * 8⁻¹ * 2⁻¹) := by
      simp only [div_eq_mul_inv, pow_two]
      ac_rfl
    _ = c * (r * r) * (128 : ENNReal)⁻¹ := by
      rw [hconstant]
    _ = c * r ^ 2 / 128 := by
      simp only [div_eq_mul_inv, pow_two]

/-- The normalized B2 lower-volume cardinality is exactly `X / 128`, where
`X = |activeCoarse| rho^2`. -/
theorem activeRestrictedCoarse_normalizedCard_eq_cardScaleMass_div_128
    (S : StickyScaleCover fine rho) :
    (Fintype.card
          (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal) *
        ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2) =
      (activeCoarseCardScaleMass S : ENNReal) / 128 := by
  rw [Fintype.card_fin]
  simp only [activeFineRestrictedScaleCover, activeCoarseCardScaleMass,
    ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0)]
  exact ennreal_card_eighth_sq_half
    (S.activeCoarse.card : ENNReal) (rho : ENNReal)

/-- A lower bound `q <= X` and a scalar budget at `q / 128` imply the exact
base-budget premise used by the B2 Frostman selector on the same coarse
family. -/
theorem activeFrozenCoarse_baseBudget_of_cardScaleMassLower
    (S : StickyScaleCover fine rho)
    {q C loss : ENNReal} {eta : Real}
    (hXLower : q <= (activeCoarseCardScaleMass S : ENNReal))
    (hscalar :
      loss * ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) * (q / 128)) :
    loss * ((128 * C) * volume (unitBallBody : Set Space)) <=
      ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
        ((Fintype.card
            (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal) *
          ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2)) := by
  calc
    loss * ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) * (q / 128) := hscalar
    _ <= ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
        ((activeCoarseCardScaleMass S : ENNReal) / 128) :=
      mul_le_mul' le_rfl (ENNReal.div_le_div_right hXLower 128)
    _ = ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
        ((Fintype.card
            (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal) *
          ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2)) := by
      rw [activeRestrictedCoarse_normalizedCard_eq_cardScaleMass_div_128]

#print axioms activeRestrictedCoarse_normalizedCard_eq_cardScaleMass_div_128
#print axioms activeFrozenCoarse_baseBudget_of_cardScaleMassLower

end
end Family8FrozenCoarseB2CardScaleBaseBudgetV6
