import Family8Grounding.Family8CanonicalBufferedGlobalFirstFactorPowerInputsV1
import Family8Grounding.Family8IdentifiedDividingWitnessActiveLogLossV3
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveMiddlePowerInputsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1.StickyScaleCover
open Family8CanonicalBufferedGlobalFirstFactorPowerInputsV1.Witness
open Family8CanonicalBufferedGlobalRelativeScaleGainV1
open Family8IdentifiedDividingWitnessActiveLogLossV3.Witness
open Family8FrozenComparableActualAverageMassDensityV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Tau-active middle-factor power inputs

These are the three object-independent inputs needed to run the contracted-
John relative-power endpoint on the literal bounded tau-active assembly.  In
particular, active-fine restriction only reindexes the coarse family, so its
card-scale mass has the same `1024 * CKT` bound as the canonical cover.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem canonicalBufferedTauActive_restricted_cardScaleMass_le_1024_mul
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    {CKT : ENNReal}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT) :
    let U0 := canonicalBufferedTauActiveCover D hD Cmulti Sseq W
      P.epsilon_pos.le hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <= 1024 * CKT := by
  dsimp only
  let U0 := canonicalBufferedTauActiveCover D hD Cmulti Sseq W
    P.epsilon_pos.le hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hKT : U0.IsKatzTaoAtScale CKT :=
    hKTEvery (canonicalBufferedRadius W)
      ((Sseq.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
      (canonicalBufferedRadius_le_one W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf)
  have hfamily : U0.activeCoarseFamily = G.activeCoarseFamily :=
    canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global
      D hD Cmulti Sseq W P.epsilon_pos.le hepsilonHalf
  have hcontained : forall k,
      (U0.activeCoarseFamily k : Set Space) <=
        (closedBallFourBody : Set Space) := by
    intro k
    rw [hfamily]
    exact activeCoarseFamily_body_subset_closedBall_four
      D hD G (hbufferedHalf.trans (by norm_num)) k
  have hX0 : (activeCoarseCardScaleMass U0 : ENNReal) <= 1024 * CKT :=
    activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale_of_contained
      U0 hbufferedHalf hKT hcontained
  have hcard : U.activeCoarse.card = U0.activeCoarse.card := by
    change (Finset.univ : Finset (Fin U0.activeCoarse.card)).card =
      U0.activeCoarse.card
    simp only [Finset.card_univ, Fintype.card_fin]
  have hEq : activeCoarseCardScaleMass U =
      activeCoarseCardScaleMass U0 := by
    simp only [activeCoarseCardScaleMass, hcard]
  rw [hEq]
  exact hX0

theorem canonicalBufferedTauActive_restricted_cardScaleMass_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    {CKT : ENNReal}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    {etaKT absorbExp : Real} (habsorbExp : 0 < absorbExp)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hsmall : delta <= canonicalGlobalXPowerThreshold absorbExp) :
    let U0 := canonicalBufferedTauActiveCover D hD Cmulti Sseq W
      P.epsilon_pos.le hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <=
      (delta : ENNReal) ^ (-(etaKT + absorbExp)) := by
  dsimp only
  have hX :=
    canonicalBufferedTauActive_restricted_cardScaleMass_le_1024_mul
      D hD Cmulti Sseq P W hepsilonHalf hbufferedHalf hKTEvery
  have hconstant : (1024 : ENNReal) <=
      (delta : ENNReal) ^ (-absorbExp) :=
    finiteConstant_le_delta_negativePower (by norm_num)
      habsorbExp hD.delta_pos hsmall
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    (activeCoarseCardScaleMass
        (activeFineRestrictedScaleCover
          (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
            P.epsilon_pos.le hepsilonHalf)) : ENNReal) <= 1024 * CKT := hX
    _ <= (delta : ENNReal) ^ (-absorbExp) *
        (delta : ENNReal) ^ (-etaKT) := mul_le_mul' hconstant hCKT
    _ = (delta : ENNReal) ^ (-(etaKT + absorbExp)) := by
      rw [show -(etaKT + absorbExp) = -absorbExp + -etaKT by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

theorem canonicalBufferedTauActive_ratio_power_inputs
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq) :
    let q : ENNReal :=
      (Sseq.tau W.m : ENNReal) / (canonicalBufferedRadius W : ENNReal)
    q ≠ 0 /\ q ≠ ∞ /\
      q <= (delta : ENNReal) ^ (P.epsilon ^ 2) := by
  dsimp only
  have htau : 0 < Sseq.tau W.m :=
    hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  have hb : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  constructor
  · exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr htau.ne', ENNReal.coe_ne_top⟩
  constructor
  · exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hb.ne')
  · rw [<- ENNReal.coe_div hb.ne',
      <- ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne', ENNReal.coe_le_coe]
    exact tau_div_canonicalLowerBufferedScale_le_rpow_sq
      hD.delta_pos (Sseq.delta_le_tau W.m) (Sseq.tau_le_theta W.m)
        P.epsilon_pos.le W.long

theorem canonicalBufferedTauActive_frozenLoss_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {lossExp : Real} (hlossExp : 0 < lossExp)
    (hsmall : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossExp) :
    let U0 := canonicalBufferedTauActiveCover D hD Cmulti Sseq W
      P.epsilon_pos.le hepsilonHalf
    (frozenComparableLoss {i // i ∈ U0.activeFine}
        (Fin U0.activeCoarse.card) : ENNReal) <=
      (delta : ENNReal) ^ (-lossExp) := by
  exact canonicalBuffered_activeFrozenLoss_le_original_rpow
    D hD Cmulti Sseq P W hepsilonHalf hlossExp hsmall

#print axioms canonicalBufferedTauActive_restricted_cardScaleMass_le_1024_mul
#print axioms canonicalBufferedTauActive_restricted_cardScaleMass_le_power
#print axioms canonicalBufferedTauActive_ratio_power_inputs
#print axioms canonicalBufferedTauActive_frozenLoss_le_power

end Witness
end
end Family8CanonicalBufferedTauActiveMiddlePowerInputsV1
