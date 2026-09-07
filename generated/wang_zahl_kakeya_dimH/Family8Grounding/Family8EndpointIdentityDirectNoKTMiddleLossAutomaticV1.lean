import Family8Grounding.Family8FirstCrossingMiddleScalarAbsorptionV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# Automatic G4 middle-loss absorption for the direct no-KT LongCore route

The direct no-KT composer previously exposed one callback for every exact
outer assembly and every selected-cardinality value.  Its only assembly
dependence is the frozen logarithmic loss.  This file absorbs that loss,
together with the literal coefficient four, at the source scale.

The resulting theorem has exactly the callback shape needed by the composer.
It leaves only two honest scalar assumptions: a finite-constant small-scale
threshold and an exponent budget.  No cancellation of the common Frostman
factor is used, so the result remains valid when that factor is zero or top.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityDirectNoKTMiddleLossAutomaticV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8FirstCrossingMiddleScalarAbsorptionV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- If one copy of the assembly loss and the fixed coefficient four each cost
`lossExp`, then the outer `globalEta` power absorbs both costs and reaches the
stage exponent.  This is the scalar core of the automatic G4 closure. -/
theorem four_mul_loss_mul_globalPower_le_stagePower
    {delta : NNReal} {loss : ENNReal}
    {lossExp globalEta stageEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hlossExp : 0 < lossExp)
    (hsmallFour : delta ≤
      finiteConstantSmallDeltaThreshold (4 : ENNReal) lossExp)
    (hLoss : loss ≤ (delta : ENNReal) ^ (-lossExp))
    (hExponentBudget :
      10 * stageEta + 2 * lossExp ≤ 10 * globalEta) :
    (4 * loss) * (delta : ENNReal) ^ (10 * globalEta) ≤
      (delta : ENNReal) ^ (10 * stageEta) := by
  have hfour : (4 : ENNReal) ≤
      (delta : ENNReal) ^ (-lossExp) := by
    exact finiteConstant_le_delta_negativePower
      (K := (4 : ENNReal)) (by norm_num) hlossExp hdelta hsmallFour
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hcoefficient : 4 * loss ≤
      (delta : ENNReal) ^ (-(2 * lossExp)) := by
    calc
      4 * loss ≤
          (delta : ENNReal) ^ (-lossExp) *
            (delta : ENNReal) ^ (-lossExp) :=
        mul_le_mul' hfour hLoss
      _ = (delta : ENNReal) ^ (-(2 * lossExp)) := by
        rw [← ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
        congr 1
        ring
  have hscalar :=
    outer_mul_coefficient_mul_ratio_le_globalTenEta
      (delta := delta)
      (outer := (delta : ENNReal) ^ (10 * globalEta))
      (coefficient := 4 * loss) (ratio := 1)
      (aOuter := 10 * globalEta) (aCoefficient := 2 * lossExp)
      (aRatio := 0) (eta := stageEta)
      hdelta hdeltaOne le_rfl hcoefficient (by simp) (by linarith)
  calc
    (4 * loss) * (delta : ENNReal) ^ (10 * globalEta) =
        (delta : ENNReal) ^ (10 * globalEta) * ((4 * loss) * 1) := by
      ac_rfl
    _ ≤ (delta : ENNReal) ^ (10 * stageEta) := hscalar

/-- Multiplication by the common scale-count Frostman factor preserves the
automatic scalar G4 bound; no division or nonzero assumption is required. -/
theorem four_mul_loss_middleFactor_le_stageFactor
    {delta fine coarse : NNReal} {loss : ENNReal} {tubeCount : Nat}
    {gamma lossExp globalEta stageEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hlossExp : 0 < lossExp)
    (hsmallFour : delta ≤
      finiteConstantSmallDeltaThreshold (4 : ENNReal) lossExp)
    (hLoss : loss ≤ (delta : ENNReal) ^ (-lossExp))
    (hExponentBudget :
      10 * stageEta + 2 * lossExp ≤ 10 * globalEta) :
    (4 * loss) *
        ((delta : ENNReal) ^ (10 * globalEta) *
          sectionEightScaleCountFrostmanFactor
            fine coarse tubeCount gamma) ≤
      (delta : ENNReal) ^ (10 * stageEta) *
        sectionEightScaleCountFrostmanFactor fine coarse tubeCount gamma := by
  have hcore := four_mul_loss_mul_globalPower_le_stagePower
    hdelta hdeltaOne hlossExp hsmallFour hLoss hExponentBudget
  calc
    (4 * loss) *
        ((delta : ENNReal) ^ (10 * globalEta) *
          sectionEightScaleCountFrostmanFactor fine coarse tubeCount gamma) =
      ((4 * loss) * (delta : ENNReal) ^ (10 * globalEta)) *
        sectionEightScaleCountFrostmanFactor fine coarse tubeCount gamma := by
      ac_rfl
    _ ≤ (delta : ENNReal) ^ (10 * stageEta) *
        sectionEightScaleCountFrostmanFactor fine coarse tubeCount gamma :=
      mul_le_mul' hcore le_rfl

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The normalized canonical tau-active frozen-loss theorem, transported
through the exact assembly-loss identity, supplies the complete G4 callback
used by the direct no-KT LongCore composer. -/
theorem canonicalBufferedTauActive_middleLoss_callback
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    {lossExp globalEta stageEta : Real}
    (hlossExp : 0 < lossExp)
    (hsmallLoss : delta ≤
      activeFrozenComparableLossAbsorptionThreshold lossExp)
    (hsmallFour : delta ≤
      finiteConstantSmallDeltaThreshold (4 : ENNReal) lossExp)
    (hExponentBudget :
      10 * stageEta + 2 * lossExp ≤ 10 * globalEta) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W P.epsilon_pos.le hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    ∀ assemblyLoss : Nat,
      assemblyLoss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) →
      ∀ tubeCount : Nat,
        (4 * (assemblyLoss : ENNReal)) *
            ((delta : ENNReal) ^ (10 * globalEta) *
              sectionEightScaleCountFrostmanFactor
                (S.tau W.m) (canonicalBufferedRadius W)
                tubeCount gamma) ≤
          (delta : ENNReal) ^ (10 * stageEta) *
            sectionEightScaleCountFrostmanFactor
              (S.tau W.m) (canonicalBufferedRadius W)
              tubeCount gamma := by
  dsimp only
  let U0 := canonicalBufferedTauActiveCover
    D hD C S W P.epsilon_pos.le hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  intro assemblyLoss hAssemblyLoss tubeCount
  have hLossRaw := canonicalBufferedTauActive_frozenLoss_le_power
    D hD C S P W hepsilonHalf hlossExp hsmallLoss
  have hLoss : (assemblyLoss : ENNReal) ≤
      (delta : ENNReal) ^ (-lossExp) := by
    rw [hAssemblyLoss]
    change (frozenComparableLoss {i // i ∈ U0.activeFine}
      (Fin U.coarseCard) : ENNReal) ≤
        (delta : ENNReal) ^ (-lossExp)
    have hcoarseCard : U.coarseCard = U0.activeCoarse.card := rfl
    rw [hcoarseCard]
    exact hLossRaw
  exact four_mul_loss_middleFactor_le_stageFactor
    hD.delta_pos (hD.delta_le_half.trans (by norm_num))
      hlossExp hsmallFour hLoss hExponentBudget

#print axioms four_mul_loss_mul_globalPower_le_stagePower
#print axioms four_mul_loss_middleFactor_le_stageFactor
#print axioms canonicalBufferedTauActive_middleLoss_callback

end
end Family8EndpointIdentityDirectNoKTMiddleLossAutomaticV1
