import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPowerV5
import Family8Grounding.Family8FiniteRandomRigidMotionB2DensityTransportV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossSourceExponentV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
open Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPowerV5

noncomputable section

/-!
# Greedy-loss power after inserting the source Katz--Tao exponent

If the source concentration constant is at most `delta ^ (-sourceEta)`, the
automatic greedy loss has the single normalized-radius exponent
`17 + tailEta + sourceEta`.  Both a real and an `ENNReal` version are exposed
so the result can feed the exact density cross-budget without casts hidden in
later connectors.
-/

/-- The finite coefficient after replacing `128 C` by the source exponent
power and absorbing the literal `+2`. -/
def fixedJohnGreedyLossSourcePowerConstant (tailEta : Real) : Real :=
  fixedJohnGreedyLossPowerConstant tailEta * 128 + 2

theorem fixedJohnGreedyLossSourcePowerConstant_nonneg (tailEta : Real) :
    0 ≤ fixedJohnGreedyLossSourcePowerConstant tailEta := by
  unfold fixedJohnGreedyLossSourcePowerConstant
  have hK := fixedJohnGreedyLossPowerConstant_nonneg tailEta
  positivity

/-- Real-valued source-exponent envelope. -/
theorem fixedJohnAutomaticGreedyLoss_cast_le_sourceExponentPower
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} {sourceEta tailEta : Real}
    (hsourceEta : 0 ≤ sourceEta) (htailEta : 0 < tailEta)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hC : C ≤ (delta : ENNReal) ^ (-sourceEta)) :
    (fixedJohnAutomaticGreedyLoss D hD : Real) ≤
      fixedJohnGreedyLossSourcePowerConstant tailEta *
        (((delta / 8 : NNReal) : Real) ^
          (-(17 + tailEta + sourceEta))) := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hrhoOne : rho ≤ 1 := by
    dsimp only [rho]
    exact_mod_cast
      ((div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8)).trans
          (hD.delta_le_half.trans (by norm_num : (2 : NNReal)⁻¹ ≤ 1)))
  have hrhoDelta : rho ≤ (delta : Real) := by
    dsimp only [rho]
    exact_mod_cast div_le_self (show 0 ≤ delta from bot_le)
      (by norm_num : (1 : NNReal) ≤ 8)
  have hdeltaTop : (delta : ENNReal) ^ (-sourceEta) ≠ ∞ := by
    rw [← ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne' (-sourceEta)]
    exact ENNReal.coe_ne_top
  have hCtop : C ≠ ∞ := ne_top_of_le_ne_top hdeltaTop hC
  have hCRealDelta : C.toReal ≤ (delta : Real) ^ (-sourceEta) := by
    have hto := (ENNReal.toReal_le_toReal hCtop hdeltaTop).2 hC
    rw [← ENNReal.toReal_rpow] at hto
    simpa using hto
  have hdeltaRhoPower :
      (delta : Real) ^ (-sourceEta) ≤ rho ^ (-sourceEta) :=
    Real.rpow_le_rpow_of_nonpos hrho hrhoDelta
      (neg_nonpos.mpr hsourceEta)
  have hCRealRho : C.toReal ≤ rho ^ (-sourceEta) :=
    hCRealDelta.trans hdeltaRhoPower
  have hM : (128 * C).toReal ≤ 128 * rho ^ (-sourceEta) := by
    calc
      (128 * C).toReal = 128 * C.toReal := by
        norm_num [ENNReal.toReal_mul]
      _ ≤ 128 * rho ^ (-sourceEta) := by gcongr
  have hloss :=
    fixedJohnAutomaticGreedyLoss_cast_le_sourceKT_power
      D hD hCtop hKT htailEta
  have hpowerOne :
      1 ≤ rho ^ (-(17 + tailEta + sourceEta)) := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrhoOne
    linarith
  have hpowers :
      rho ^ (-sourceEta) * rho ^ (-(17 + tailEta)) =
        rho ^ (-(17 + tailEta + sourceEta)) := by
    rw [← Real.rpow_add hrho]
    congr 1
    ring
  calc
    (fixedJohnAutomaticGreedyLoss D hD : Real) ≤
        fixedJohnGreedyLossPowerConstant tailEta * (128 * C).toReal *
            rho ^ (-(17 + tailEta)) + 2 := by
      simpa only [rho] using hloss
    _ ≤ fixedJohnGreedyLossPowerConstant tailEta *
          (128 * rho ^ (-sourceEta)) *
            rho ^ (-(17 + tailEta)) + 2 := by
      gcongr
      exact fixedJohnGreedyLossPowerConstant_nonneg tailEta
    _ = (fixedJohnGreedyLossPowerConstant tailEta * 128) *
          rho ^ (-(17 + tailEta + sourceEta)) + 2 := by
      rw [← hpowers]
      ring
    _ ≤ (fixedJohnGreedyLossPowerConstant tailEta * 128) *
          rho ^ (-(17 + tailEta + sourceEta)) +
        2 * rho ^ (-(17 + tailEta + sourceEta)) := by
      gcongr
      simpa using hpowerOne
    _ = fixedJohnGreedyLossSourcePowerConstant tailEta *
          rho ^ (-(17 + tailEta + sourceEta)) := by
      unfold fixedJohnGreedyLossSourcePowerConstant
      ring

/-- `ENNReal` spelling of the source-exponent envelope consumed by the
division-free density and base budgets. -/
theorem fixedJohnAutomaticGreedyLoss_le_sourceExponentPower
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} {sourceEta tailEta : Real}
    (hsourceEta : 0 ≤ sourceEta) (htailEta : 0 < tailEta)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hC : C ≤ (delta : ENNReal) ^ (-sourceEta)) :
    (fixedJohnAutomaticGreedyLoss D hD : ENNReal) ≤
      ENNReal.ofReal (fixedJohnGreedyLossSourcePowerConstant tailEta) *
        (((delta / 8 : NNReal) : ENNReal) ^
          (-(17 + tailEta + sourceEta))) := by
  have hreal := fixedJohnAutomaticGreedyLoss_cast_le_sourceExponentPower
    D hD hsourceEta htailEta hKT hC
  have hrho : 0 < ((delta / 8 : NNReal) : Real) := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hrpow :
      (((delta / 8 : NNReal) : ENNReal) ^
          (-(17 + tailEta + sourceEta))) =
        ENNReal.ofReal
          (((delta / 8 : NNReal) : Real) ^
            (-(17 + tailEta + sourceEta))) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_rpow_of_pos hrho
  rw [hrpow, ← ENNReal.ofReal_mul
    (fixedJohnGreedyLossSourcePowerConstant_nonneg tailEta)]
  simpa using ENNReal.ofReal_le_ofReal hreal

#print axioms fixedJohnAutomaticGreedyLoss_cast_le_sourceExponentPower
#print axioms fixedJohnAutomaticGreedyLoss_le_sourceExponentPower

end
end Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossSourceExponentV4
