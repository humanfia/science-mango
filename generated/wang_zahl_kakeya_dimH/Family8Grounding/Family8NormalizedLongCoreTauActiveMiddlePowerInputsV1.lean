import Family8Grounding.Family8CanonicalBufferedGlobalFirstFactorPowerInputsV1
import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1
import Family8Grounding.Family8FrozenComparableLogLossSourceCardTransferV2
import Mathlib.Tactic

/-!
# Tau-active middle power inputs on the normalized long core

The active coarse card-scale mass and the bounded assembly's two logarithmic
losses depend only on the literal `tau -> b` cover and ambient source-card
bound.  They therefore port to the core witness without either discarded
outside estimate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8CanonicalBufferedGlobalFirstFactorPowerInputsV1.Witness
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableLogLossSourceCardTransferV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover
open Family8StickyParentHullVolumeBoundV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Reindexing the active `tau` parents cannot increase the ambient source
index cardinality. -/
theorem tauActiveCoarseDatum_indexCard_le_source
    (D : ActualTubeDatum delta index)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S) :
    Fintype.card {k // k ∈ (tauScaleCover D C S W).activeCoarse} <=
      Fintype.card index := by
  rw [Fintype.card_coe]
  calc
    (tauScaleCover D C S W).activeCoarse.card <=
        (tauScaleCover D C S W).activeFine.card :=
      Family8StickyActiveIndexFrozenComparableAssemblyV5.activeCoarse_card_le_activeFine_card
        (tauScaleCover D C S W)
    _ <= Fintype.card index := by
      simpa only [Finset.card_univ] using
        Finset.card_le_card
          (Finset.subset_univ (tauScaleCover D C S W).activeFine)

/-- Both active logarithmic factors are absorbed at the original scale. -/
theorem canonicalBufferedTauActive_frozenLoss_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {lossExp : Real} (hlossExp : 0 < lossExp)
    (hsmall : delta <= activeFrozenComparableLossAbsorptionThreshold lossExp) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W P.epsilon_pos.le hepsilonHalf
    (frozenComparableLoss {i // i ∈ U0.activeFine}
        (Fin U0.activeCoarse.card) : ENNReal) <=
      (delta : ENNReal) ^ (-lossExp) := by
  dsimp only
  exact activeFrozenComparableLoss_le_rpow_of_indexCard_le_source
    D hD
      (canonicalBufferedTauActiveCover
        D hD C S W P.epsilon_pos.le hepsilonHalf)
      (tauActiveCoarseDatum_indexCard_le_source D C S P W)
      hlossExp hsmall

/-- Restricting to the fully active tau-parent subtype preserves the
card-scale mass, which has the native `1024 * CKT` bound. -/
theorem canonicalBufferedTauActive_restricted_cardScaleMass_le_1024_mul
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    {CKT : ENNReal}
    (hKTEvery : C.base.IsKatzTaoAtEveryScale CKT) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W P.epsilon_pos.le hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <= 1024 * CKT := by
  dsimp only
  let U0 := canonicalBufferedTauActiveCover
    D hD C S W P.epsilon_pos.le hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hKT : U0.IsKatzTaoAtScale CKT :=
    hKTEvery (canonicalBufferedRadius W)
      ((S.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
      (canonicalBufferedRadius_le_one W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf)
  have hfamily : U0.activeCoarseFamily = G.activeCoarseFamily :=
    canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global
      D hD C S W P.epsilon_pos.le hepsilonHalf
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

/-- Absorb the fixed factor `1024` into an arbitrarily small extra power. -/
theorem canonicalBufferedTauActive_restricted_cardScaleMass_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    {CKT : ENNReal}
    (hKTEvery : C.base.IsKatzTaoAtEveryScale CKT)
    {etaKT absorbExp : Real} (habsorbExp : 0 < absorbExp)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hsmall : delta <= canonicalGlobalXPowerThreshold absorbExp) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W P.epsilon_pos.le hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <=
      (delta : ENNReal) ^ (-(etaKT + absorbExp)) := by
  dsimp only
  have hX :=
    canonicalBufferedTauActive_restricted_cardScaleMass_le_1024_mul
      D hD C S P W hepsilonHalf hbufferedHalf hKTEvery
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
          (canonicalBufferedTauActiveCover
            D hD C S W P.epsilon_pos.le hepsilonHalf)) : ENNReal) <=
        1024 * CKT := hX
    _ <= (delta : ENNReal) ^ (-absorbExp) *
        (delta : ENNReal) ^ (-etaKT) := mul_le_mul' hconstant hCKT
    _ = (delta : ENNReal) ^ (-(etaKT + absorbExp)) := by
      rw [show -(etaKT + absorbExp) = -absorbExp + -etaKT by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

#print axioms tauActiveCoarseDatum_indexCard_le_source
#print axioms canonicalBufferedTauActive_frozenLoss_le_power
#print axioms canonicalBufferedTauActive_restricted_cardScaleMass_le_1024_mul
#print axioms canonicalBufferedTauActive_restricted_cardScaleMass_le_power

end
end Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
