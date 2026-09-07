import Family8Grounding.Family8FixedJohnMaxThresholdGreedyLossV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FixedJohnMaxThresholdSourcePowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPolynomialV3
open Family8FiniteRandomRigidMotionPaperFixedJohnSourceKTBudgetV5
open Family8FiniteRandomRigidMotionPaperFixedJohnTailPowerV2
open Family8FixedJohnMaxThresholdGreedyLossV1

noncomputable section

/-!
# Source-power envelope for the maximum-threshold greedy loss

The catalogue cardinality now occurs only inside a logarithm.  One individual
paper cap contributes the source concentration and exactly two inverse powers
of the normalized tube radius.
-/

theorem fixedJohnMaxPaperCap_le_absolute
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    fixedJohnMaxPaperCap (fixedJohnPackingGridVector D hD) D hD ≤
      (fixedJohnPackingMaximalConcentration D hD).toReal *
          (2304 : Real) ^ 3 /
        ((((delta / 8 : NNReal) : Real) ^ 2) / 2) := by
  unfold fixedJohnMaxPaperCap
  rw [Finset.fold_max_le]
  constructor
  · positivity
  · intro K _hK
    exact fixedJohnTranslationPaperCap_le_absolute D hD K

theorem fixedJohnMaxAutomaticGreedyLoss_cast_le_sourceKT_absolute
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hC : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily) :
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) ≤
      fixedJohnTailParameter D hD *
        ((128 * C).toReal * (2304 : Real) ^ 3 /
          ((((delta / 8 : NNReal) : Real) ^ 2) / 2)) +
        2 := by
  have hM := fixedJohnPackingMaximalConcentration_toReal_le_128_mul
    D hD hC hKT
  have hden : 0 < ((((delta / 8 : NNReal) : Real) ^ 2) / 2) := by
    have hrho : 0 < ((delta / 8 : NNReal) : Real) := by
      exact_mod_cast admissibleNormalizedRadiusPos hD
    positivity
  apply (fixedJohnMaxAutomaticGreedyLoss_cast_le_envelope D hD).trans
  gcongr
  · exact zero_le_one.trans (one_le_fixedJohnTailParameter D hD)
  · exact (fixedJohnMaxPaperCap_le_absolute D hD).trans (by gcongr)

def fixedJohnMaxGreedyLossPowerConstant (tailEta : Real) : Real :=
  fixedJohnTailPowerConstant tailEta * (2304 : Real) ^ 3 * 2

theorem fixedJohnMaxGreedyLossPowerConstant_nonneg (tailEta : Real) :
    0 ≤ fixedJohnMaxGreedyLossPowerConstant tailEta := by
  have htail := fixedJohnTailPowerConstant_nonneg tailEta
  unfold fixedJohnMaxGreedyLossPowerConstant
  positivity

theorem fixedJohnMaxAutomaticGreedyLoss_cast_le_sourceKT_power
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hC : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    {tailEta : Real} (htailEta : 0 < tailEta) :
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) ≤
      fixedJohnMaxGreedyLossPowerConstant tailEta * (128 * C).toReal *
          (((delta / 8 : NNReal) : Real) ^ (-(2 + tailEta))) +
        2 := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  let M : Real := (128 * C).toReal
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have htail := fixedJohnTailParameter_le_power D hD htailEta
  have htube :
      (M * (2304 : Real) ^ 3) / (rho ^ 2 / 2) =
        (M * (2304 : Real) ^ 3 * 2) * rho ^ (-2 : Real) := by
    rw [Real.rpow_neg hrho.le]
    field_simp
    rw [Real.rpow_two]
  have hpowers :
      rho ^ (-tailEta) * rho ^ (-2 : Real) =
        rho ^ (-(2 + tailEta)) := by
    rw [← Real.rpow_add hrho]
    congr 1
    ring
  have hinside :
      fixedJohnTailParameter D hD *
          (M * (2304 : Real) ^ 3 / (rho ^ 2 / 2)) ≤
        fixedJohnMaxGreedyLossPowerConstant tailEta * M *
          rho ^ (-(2 + tailEta)) := by
    calc
      fixedJohnTailParameter D hD *
            (M * (2304 : Real) ^ 3 / (rho ^ 2 / 2)) ≤
          (fixedJohnTailPowerConstant tailEta * rho ^ (-tailEta)) *
            (M * (2304 : Real) ^ 3 / (rho ^ 2 / 2)) := by
        gcongr
      _ = fixedJohnMaxGreedyLossPowerConstant tailEta * M *
            rho ^ (-(2 + tailEta)) := by
        rw [htube]
        unfold fixedJohnMaxGreedyLossPowerConstant
        rw [← hpowers]
        ring
  apply
    (fixedJohnMaxAutomaticGreedyLoss_cast_le_sourceKT_absolute
      D hD hC hKT).trans
  dsimp only [rho, M] at hinside ⊢
  simpa only [add_comm] using add_le_add_right hinside 2

def fixedJohnMaxGreedyLossSourcePowerConstant (tailEta : Real) : Real :=
  fixedJohnMaxGreedyLossPowerConstant tailEta * 128 + 2

theorem fixedJohnMaxGreedyLossSourcePowerConstant_nonneg (tailEta : Real) :
    0 ≤ fixedJohnMaxGreedyLossSourcePowerConstant tailEta := by
  unfold fixedJohnMaxGreedyLossSourcePowerConstant
  have hK := fixedJohnMaxGreedyLossPowerConstant_nonneg tailEta
  positivity

theorem fixedJohnMaxAutomaticGreedyLoss_cast_le_sourceExponentPower
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} {sourceEta tailEta : Real}
    (hsourceEta : 0 ≤ sourceEta) (htailEta : 0 < tailEta)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hC : C ≤ (delta : ENNReal) ^ (-sourceEta)) :
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) ≤
      fixedJohnMaxGreedyLossSourcePowerConstant tailEta *
        (((delta / 8 : NNReal) : Real) ^
          (-(2 + tailEta + sourceEta))) := by
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
  have hloss := fixedJohnMaxAutomaticGreedyLoss_cast_le_sourceKT_power
    D hD hCtop hKT htailEta
  have hpowerOne :
      1 ≤ rho ^ (-(2 + tailEta + sourceEta)) := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrhoOne
    linarith
  have hpowers :
      rho ^ (-sourceEta) * rho ^ (-(2 + tailEta)) =
        rho ^ (-(2 + tailEta + sourceEta)) := by
    rw [← Real.rpow_add hrho]
    congr 1
    ring
  calc
    (fixedJohnMaxAutomaticGreedyLoss D hD : Real) ≤
        fixedJohnMaxGreedyLossPowerConstant tailEta * (128 * C).toReal *
            rho ^ (-(2 + tailEta)) + 2 := by
      simpa only [rho] using hloss
    _ ≤ fixedJohnMaxGreedyLossPowerConstant tailEta *
          (128 * rho ^ (-sourceEta)) *
            rho ^ (-(2 + tailEta)) + 2 := by
      gcongr
      exact fixedJohnMaxGreedyLossPowerConstant_nonneg tailEta
    _ = (fixedJohnMaxGreedyLossPowerConstant tailEta * 128) *
          rho ^ (-(2 + tailEta + sourceEta)) + 2 := by
      rw [← hpowers]
      ring
    _ ≤ (fixedJohnMaxGreedyLossPowerConstant tailEta * 128) *
          rho ^ (-(2 + tailEta + sourceEta)) +
        2 * rho ^ (-(2 + tailEta + sourceEta)) := by
      gcongr
      simpa using hpowerOne
    _ = fixedJohnMaxGreedyLossSourcePowerConstant tailEta *
          rho ^ (-(2 + tailEta + sourceEta)) := by
      unfold fixedJohnMaxGreedyLossSourcePowerConstant
      ring

theorem fixedJohnMaxAutomaticGreedyLoss_le_sourceExponentPower
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} {sourceEta tailEta : Real}
    (hsourceEta : 0 ≤ sourceEta) (htailEta : 0 < tailEta)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hC : C ≤ (delta : ENNReal) ^ (-sourceEta)) :
    (fixedJohnMaxAutomaticGreedyLoss D hD : ENNReal) ≤
      ENNReal.ofReal
          (fixedJohnMaxGreedyLossSourcePowerConstant tailEta) *
        (((delta / 8 : NNReal) : ENNReal) ^
          (-(2 + tailEta + sourceEta))) := by
  have hreal :=
    fixedJohnMaxAutomaticGreedyLoss_cast_le_sourceExponentPower
      D hD hsourceEta htailEta hKT hC
  have hrho : 0 < ((delta / 8 : NNReal) : Real) := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hrpow :
      (((delta / 8 : NNReal) : ENNReal) ^
          (-(2 + tailEta + sourceEta))) =
        ENNReal.ofReal
          (((delta / 8 : NNReal) : Real) ^
            (-(2 + tailEta + sourceEta))) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_rpow_of_pos hrho
  rw [hrpow, ← ENNReal.ofReal_mul
    (fixedJohnMaxGreedyLossSourcePowerConstant_nonneg tailEta)]
  simpa using ENNReal.ofReal_le_ofReal hreal

#print axioms fixedJohnMaxPaperCap_le_absolute
#print axioms fixedJohnMaxAutomaticGreedyLoss_cast_le_sourceKT_absolute
#print axioms fixedJohnMaxAutomaticGreedyLoss_cast_le_sourceKT_power
#print axioms fixedJohnMaxAutomaticGreedyLoss_cast_le_sourceExponentPower
#print axioms fixedJohnMaxAutomaticGreedyLoss_le_sourceExponentPower

end
end Family8FixedJohnMaxThresholdSourcePowerV1
