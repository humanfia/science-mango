import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnSourceKTBudgetV5
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnTailPowerV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPowerV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
open Family8FiniteRandomRigidMotionPaperFixedJohnSourceKTBudgetV5
open Family8FiniteRandomRigidMotionPaperFixedJohnTailPowerV2

noncomputable section

/-!
# Scale-power envelope for the automatic fixed-John greedy loss

This module combines the source Katz--Tao maximal-concentration transport,
the degree-fifteen catalogue bound, the two tube-volume powers, and the
arbitrarily small logarithmic tail power.  The result has one explicit
finite coefficient and the exact scale exponent `17 + tailEta`.
-/

/-- Finite coefficient left after extracting every normalized-radius power. -/
def fixedJohnGreedyLossPowerConstant (tailEta : Real) : Real :=
  fixedJohnTailPowerConstant tailEta *
    (46082 : Real) ^ 15 * (2304 : Real) ^ 3 * 2

theorem fixedJohnGreedyLossPowerConstant_nonneg (tailEta : Real) :
    0 ≤ fixedJohnGreedyLossPowerConstant tailEta := by
  have htail : 0 ≤ fixedJohnTailPowerConstant tailEta :=
    fixedJohnTailPowerConstant_nonneg tailEta
  unfold fixedJohnGreedyLossPowerConstant
  positivity

/-- The automatic loss is a finite coefficient, the source Katz--Tao
constant, and exactly `17 + tailEta` negative powers of the normalized
radius, plus the literal ceiling slack `2`. -/
theorem fixedJohnAutomaticGreedyLoss_cast_le_sourceKT_power
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hC : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    {tailEta : Real} (htailEta : 0 < tailEta) :
    (fixedJohnAutomaticGreedyLoss D hD : Real) ≤
      fixedJohnGreedyLossPowerConstant tailEta * (128 * C).toReal *
          (((delta / 8 : NNReal) : Real) ^ (-(17 + tailEta))) +
        2 := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  let M : Real := (128 * C).toReal
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have htail := fixedJohnTailParameter_le_power D hD htailEta
  have hcatalogue :
      ((46082 : Real) / rho) ^ 15 =
        (46082 : Real) ^ 15 * rho ^ (-15 : Real) := by
    rw [Real.rpow_neg hrho.le, div_pow, div_eq_mul_inv]
    exact congrArg (fun x : Real => (46082 : Real) ^ 15 * x)
      (congrArg (fun x : Real => x⁻¹)
        (Real.rpow_natCast rho 15).symm)
  have htube :
      (M * (2304 : Real) ^ 3) / (rho ^ 2 / 2) =
        (M * (2304 : Real) ^ 3 * 2) * rho ^ (-2 : Real) := by
    rw [Real.rpow_neg hrho.le]
    field_simp
    rw [Real.rpow_two]
  have hpowers :
      rho ^ (-tailEta) * rho ^ (-15 : Real) * rho ^ (-2 : Real) =
        rho ^ (-(17 + tailEta)) := by
    rw [← Real.rpow_add hrho, ← Real.rpow_add hrho]
    congr 1
    ring
  have hinside :
      fixedJohnTailParameter D hD *
          (((46082 : Real) / rho) ^ 15 *
            (M * (2304 : Real) ^ 3 / (rho ^ 2 / 2))) ≤
        fixedJohnGreedyLossPowerConstant tailEta * M *
          rho ^ (-(17 + tailEta)) := by
    calc
      fixedJohnTailParameter D hD *
          (((46082 : Real) / rho) ^ 15 *
            (M * (2304 : Real) ^ 3 / (rho ^ 2 / 2))) ≤
        (fixedJohnTailPowerConstant tailEta * rho ^ (-tailEta)) *
          (((46082 : Real) / rho) ^ 15 *
            (M * (2304 : Real) ^ 3 / (rho ^ 2 / 2))) := by
          gcongr
    _ = fixedJohnGreedyLossPowerConstant tailEta * M *
          rho ^ (-(17 + tailEta)) := by
      rw [hcatalogue, htube]
      unfold fixedJohnGreedyLossPowerConstant
      rw [← hpowers]
      ring
  apply
    (fixedJohnAutomaticGreedyLoss_cast_le_polynomial_of_source_isKatzTao
      D hD hC hKT).trans
  dsimp only [rho, M] at hinside ⊢
  simpa only [add_comm] using add_le_add_right hinside 2

#print axioms fixedJohnAutomaticGreedyLoss_cast_le_sourceKT_power

end
end Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPowerV5
