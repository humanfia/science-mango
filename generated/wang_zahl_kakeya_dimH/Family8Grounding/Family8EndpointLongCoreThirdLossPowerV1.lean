import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Family8Grounding.Family8EighthSelectedThirdFactorPowerLossAbsorptionV3
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import Mathlib.Tactic

/-!
# Source-power bound for the endpoint long-core third loss

The actual third bundle uses the fixed normalized conflict loss
`ceil (480000 * 128 * CKT) + 1`.  This module first bounds that loss by one
source-scale power, then applies the existing eighth-normalization absorption
to the literal third loss.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreThirdLossPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EighthSelectedThirdFactorPowerLossAbsorptionV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- The datum-independent coefficient in the fixed normalized conflict loss. -/
def endpointFixedConflictLossConstant : ENNReal :=
  480000 * 128 + 2

/-- One source-scale threshold absorbs both the conflict coefficient and the
fixed eighth-normalization coefficient. -/
def endpointLongCoreThirdLossSmallDeltaThreshold
    (conflictAbsorb thirdAbsorb epsilon gamma : Real) : NNReal :=
  min (finiteConstantSmallDeltaThreshold
      endpointFixedConflictLossConstant conflictAbsorb)
    (finiteConstantSmallDeltaThreshold
      (eighthSelectedThirdNormalizationLoss epsilon gamma) thirdAbsorb)

theorem endpointFixedConflictLossConstant_ne_top :
    endpointFixedConflictLossConstant ≠ ∞ := by
  norm_num [endpointFixedConflictLossConstant]

theorem endpointLongCoreThirdLossSmallDeltaThreshold_pos
    {conflictAbsorb thirdAbsorb epsilon gamma : Real} :
    0 < endpointLongCoreThirdLossSmallDeltaThreshold
      conflictAbsorb thirdAbsorb epsilon gamma := by
  exact lt_min
    (finiteConstantSmallDeltaThreshold_pos _ _)
    (finiteConstantSmallDeltaThreshold_pos _ _)

/-- The exact fixed conflict loss has one Katz--Tao exponent plus one fixed
coefficient-absorption exponent. -/
theorem fixedConflictLoss_le_delta_negativePower
    {delta : NNReal} {CKT : ENNReal}
    {etaKT conflictAbsorb : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hetaKT : 0 <= etaKT)
    (hCKTfinite : CKT ≠ ∞) (_hCKTone : 1 <= CKT)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hconflictAbsorb : 0 < conflictAbsorb)
    (hsmall : delta <= finiteConstantSmallDeltaThreshold
      endpointFixedConflictLossConstant conflictAbsorb) :
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
        ENNReal) <=
      (delta : ENNReal) ^ (-(etaKT + conflictAbsorb)) := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d <= 1 := by
    dsimp only [d]
    exact_mod_cast hdeltaOne
  have hscaledFinite : (128 : ENNReal) * CKT ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCKTfinite
  have hclosed := fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
  have hone : 1 <= d ^ (-etaKT) := by
    rw [← ENNReal.rpow_zero]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith)
  have htwo : (2 : ENNReal) <= 2 * d ^ (-etaKT) := by
    simpa only [mul_one] using
      (mul_le_mul' (show (2 : ENNReal) <= 2 from le_rfl) hone)
  have hconstant : endpointFixedConflictLossConstant <=
      d ^ (-conflictAbsorb) :=
    finiteConstant_le_delta_negativePower
      endpointFixedConflictLossConstant_ne_top hconflictAbsorb hdelta hsmall
  calc
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
        ENNReal) <= 480000 * (128 * CKT) + 2 := hclosed
    _ <= 480000 * (128 * d ^ (-etaKT)) +
          2 * d ^ (-etaKT) := by
      exact add_le_add
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl hCKT)) htwo
    _ = endpointFixedConflictLossConstant * d ^ (-etaKT) := by
      unfold endpointFixedConflictLossConstant
      ring
    _ <= d ^ (-conflictAbsorb) * d ^ (-etaKT) :=
      mul_le_mul' hconstant le_rfl
    _ = d ^ (-(etaKT + conflictAbsorb)) := by
      rw [show -(etaKT + conflictAbsorb) =
          -conflictAbsorb + -etaKT by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The exact third loss occurring in the normalized-core same-object bundle
has an explicit source-delta power bound. -/
theorem canonicalBuffered_fixedConflict_thirdLoss_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    {CKT : ENNReal}
    {etaKT conflictAbsorb thirdAbsorb epsilonThird thirdBeta : Real}
    (hetaKT : 0 <= etaKT)
    (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 <= CKT)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hconflictAbsorb : 0 < conflictAbsorb)
    (hthirdAbsorb : 0 < thirdAbsorb)
    (hepsilonThird : 0 <= epsilonThird)
    (hsmall : delta <= endpointLongCoreThirdLossSmallDeltaThreshold
      conflictAbsorb thirdAbsorb epsilonThird thirdBeta) :
    eighthSelectedThirdFactorLoss (canonicalBufferedRadius W)
        ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) epsilonThird thirdBeta <=
      (delta : ENNReal) ^
        (-((etaKT + conflictAbsorb) + epsilonThird + thirdAbsorb)) := by
  have hloss :
      ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) <=
        (delta : ENNReal) ^ (-(etaKT + conflictAbsorb)) :=
    fixedConflictLoss_le_delta_negativePower
      hD.delta_pos (hD.delta_le_half.trans (by norm_num)) hetaKT
        hCKTfinite hCKTone hCKT hconflictAbsorb
          (hsmall.trans (min_le_left _ _))
  exact eighthSelectedThirdFactorLoss_le_delta_negativePower_of_lossPower
    hD.delta_pos (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
      ((S.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
      hepsilonThird hloss hthirdAbsorb
      (hsmall.trans (min_le_right _ _))

#print axioms endpointFixedConflictLossConstant_ne_top
#print axioms endpointLongCoreThirdLossSmallDeltaThreshold_pos
#print axioms fixedConflictLoss_le_delta_negativePower
#print axioms canonicalBuffered_fixedConflict_thirdLoss_le_power

end
end Family8EndpointLongCoreThirdLossPowerV1
