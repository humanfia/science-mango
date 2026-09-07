import Family8Grounding.Family8CanonicalBufferedGlobalKatzTaoBoundedFrozenAssemblyV1
import Family8Grounding.Family8CanonicalBufferedGlobalRelativeScaleGainV1
import Family8Grounding.Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import Family8Grounding.Family8FrozenComparableLogLossSourceCardTransferV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedGlobalFirstFactorPowerInputsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8FullRefinementActualDatumV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover
open Family8FrozenComparableLogLossSourceCardTransferV2
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8FrozenComparableActualAverageMassDensityV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open Family8CanonicalBufferedGlobalRelativeScaleGainV1.Witness
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1

noncomputable section

/-!
# Canonical global inputs for the first-factor scalar producer

The four inputs are kept separate: the native parent Katz--Tao cap, the
two-level assembly logarithm, the long-interval scale gain, and the two
fixed constants.  Every conclusion is stated on the global `delta -> b`
cover, and no tau-active source-card loss is introduced.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

theorem canonicalBufferedGlobal_restricted_cardScaleMass_le_1024_mul
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hbufferedHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    {CKT : ENNReal}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT) :
    let G := canonicalBufferedGlobalCover W hD.delta_pos
      hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover G
    (activeCoarseCardScaleMass U : ENNReal) <= 1024 * CKT := by
  dsimp only
  let E := fullRefinementDatum D
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover G
  have hGKT : G.IsKatzTaoAtScale CKT :=
    hKTEvery (canonicalBufferedRadius W)
      ((Sseq.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon))
      (canonicalBufferedRadius_le_one W hD.delta_pos
        hepsilon hepsilonHalf)
  have hXG : (activeCoarseCardScaleMass G : ENNReal) <= 1024 * CKT :=
    activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale
      E (fullRefinementDatum_isAdmissible hD) G hbufferedHalf hGKT
  have hcard : U.activeCoarse.card = G.activeCoarse.card := by
    change (Finset.univ : Finset (Fin G.activeCoarse.card)).card =
      G.activeCoarse.card
    simp only [Finset.card_univ, Fintype.card_fin]
  have hEq : activeCoarseCardScaleMass U = activeCoarseCardScaleMass G := by
    simp only [activeCoarseCardScaleMass, hcard]
  rw [hEq]
  exact hXG

def canonicalGlobalXPowerThreshold (absorbExp : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 1024 absorbExp

theorem canonicalGlobalXPowerThreshold_pos (absorbExp : Real) :
    0 < canonicalGlobalXPowerThreshold absorbExp :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem canonicalBufferedGlobal_restricted_cardScaleMass_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hbufferedHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    {CKT : ENNReal}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    {etaKT absorbExp : Real} (habsorbExp : 0 < absorbExp)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hsmall : delta <= canonicalGlobalXPowerThreshold absorbExp) :
    let G := canonicalBufferedGlobalCover W hD.delta_pos
      hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover G
    (activeCoarseCardScaleMass U : ENNReal) <=
      (delta : ENNReal) ^ (-(etaKT + absorbExp)) := by
  dsimp only
  have hX := canonicalBufferedGlobal_restricted_cardScaleMass_le_1024_mul
    D hD Cmulti Sseq W hepsilon hepsilonHalf hbufferedHalf hKTEvery
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
          (canonicalBufferedGlobalCover W hD.delta_pos
            hepsilon hepsilonHalf)) : ENNReal) <= 1024 * CKT := hX
    _ <= (delta : ENNReal) ^ (-absorbExp) *
        (delta : ENNReal) ^ (-etaKT) := mul_le_mul' hconstant hCKT
    _ = (delta : ENNReal) ^ (-(etaKT + absorbExp)) := by
      rw [show -(etaKT + absorbExp) = -absorbExp + -etaKT by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

theorem canonicalBufferedGlobal_frozenLoss_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    {lossExp : Real} (hlossExp : 0 < lossExp)
    (hsmall : delta <=
      activeFrozenComparableLossAbsorptionThreshold lossExp) :
    let G := canonicalBufferedGlobalCover W hD.delta_pos
      hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover G
    (frozenComparableLoss {i // i ∈ G.activeFine}
        (Fin U.coarseCard) : ENNReal) <=
      (delta : ENNReal) ^ (-lossExp) := by
  dsimp only
  have hcoarseCard :
      (activeFineRestrictedScaleCover
        (canonicalBufferedGlobalCover W hD.delta_pos
          hepsilon hepsilonHalf)).coarseCard =
        (canonicalBufferedGlobalCover W hD.delta_pos
          hepsilon hepsilonHalf).activeCoarse.card := by
    rfl
  rw [hcoarseCard]
  exact activeFrozenComparableLoss_le_rpow_of_indexCard_le_source
    D hD (canonicalBufferedGlobalCover W hD.delta_pos
      hepsilon hepsilonHalf) (by rfl) hlossExp hsmall

theorem canonicalBufferedGlobal_ratio_power_inputs
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N epsilon eta Sseq)
    (hepsilon : 0 <= epsilon) :
    let q : ENNReal :=
      (delta : ENNReal) / (canonicalBufferedRadius W : ENNReal)
    q ≠ 0 /\ q ≠ ∞ /\ q <= (delta : ENNReal) ^ (epsilon ^ 2) := by
  dsimp only
  have hbpos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos hepsilon
  constructor
  · exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr hD.delta_pos.ne', ENNReal.coe_ne_top⟩
  constructor
  · exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hbpos.ne')
  · exact coe_delta_div_canonicalBufferedRadius_le_rpow_sq
      W hD.delta_pos hepsilon

def massPopularDensityPowerThreshold (absorbExp : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold massPopularDensityFixedConstant absorbExp

def massPopularBasePowerThreshold
    (eta p a absorbExp : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (massPopularBaseFixedConstant eta p a) absorbExp

theorem massPopularDensityFixedConstant_ne_top :
    massPopularDensityFixedConstant ≠ ∞ := by
  norm_num [massPopularDensityFixedConstant,
    Family8LongIntervalOrdinaryFiberCapNumericsV1.ordinaryFiberNatCapFixedConstant]

theorem massPopularBaseFixedConstant_ne_top (eta p a : Real) :
    massPopularBaseFixedConstant eta p a ≠ ∞ := by
  unfold massPopularBaseFixedConstant
  apply ENNReal.mul_ne_top
  · norm_num
  · apply ENNReal.rpow_ne_top_of_ne_zero
    · norm_num
    · exact ENNReal.div_ne_top (by norm_num) (by norm_num)

theorem massPopularDensityFixedConstant_le_power
    {absorbExp : Real} (habsorbExp : 0 < absorbExp)
    (hdelta : 0 < delta)
    (hsmall : delta <= massPopularDensityPowerThreshold absorbExp) :
    massPopularDensityFixedConstant <=
      (delta : ENNReal) ^ (-absorbExp) :=
  finiteConstant_le_delta_negativePower
    massPopularDensityFixedConstant_ne_top habsorbExp hdelta hsmall

theorem massPopularBaseFixedConstant_le_power
    {eta p a absorbExp : Real} (habsorbExp : 0 < absorbExp)
    (hdelta : 0 < delta)
    (hsmall : delta <=
      massPopularBasePowerThreshold eta p a absorbExp) :
    massPopularBaseFixedConstant eta p a <=
      (delta : ENNReal) ^ (-absorbExp) :=
  finiteConstant_le_delta_negativePower
    (massPopularBaseFixedConstant_ne_top eta p a)
      habsorbExp hdelta hsmall

#print axioms canonicalBufferedGlobal_restricted_cardScaleMass_le_1024_mul
#print axioms canonicalBufferedGlobal_restricted_cardScaleMass_le_power
#print axioms canonicalBufferedGlobal_frozenLoss_le_power
#print axioms canonicalBufferedGlobal_ratio_power_inputs
#print axioms massPopularDensityFixedConstant_le_power
#print axioms massPopularBaseFixedConstant_le_power

end Witness
end
end Family8CanonicalBufferedGlobalFirstFactorPowerInputsV1
