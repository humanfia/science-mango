import Family8Grounding.Family8EndpointIdentityLongCoreSourceKatzTaoBudgetV1
import Family8Grounding.Family8ActiveFineRestrictedCardScaleMassRefoldV3
import Family8Grounding.Family8IdentityCoreCanonicalBufferedLossOneAdapterV1
import Family8Grounding.Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
import Family8Grounding.Family8IdentitySourceFrostmanThirdBaseCrossedCardScaleV1
import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Mathlib.Tactic

/-!
# Correlated endpoint recomputed-third base budget

The B2 Frostman consumer needs one base inequality on one fixed endpoint
cover.  It does not need a standalone power upper bound for the source
Katz--Tao constant.  This file keeps the source Frostman cancellation and
the literal card-scale mass correlated until that complete base inequality
is formed.

The remaining exponent is honest: the conflict ceiling and its Katz--Tao
coefficient use two copies of the source Frostman exponent, while one copy
of the actual card-scale exponent remains.  No assembly or final third
conclusion is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFineRestrictedCardScaleMassRefoldV3
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8EndpointIdentityLongCoreSourceKatzTaoBudgetV1
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreCanonicalBufferedLossOneAdapterV1
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8IdentitySourceFrostmanThirdBaseCrossedCardScaleV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The single fixed coefficient used after the conflict ceiling, the
source-Frostman cancellation, and the eighth normalization are kept
together. -/
def endpointCorrelatedBaseFixedConstant : ENNReal :=
  (480000 * 128 * 128 + 2) * 2097152

def endpointCorrelatedBaseThreshold (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold endpointCorrelatedBaseFixedConstant
    absorbEta

theorem endpointCorrelatedBaseFixedConstant_ne_top :
    endpointCorrelatedBaseFixedConstant ≠ ∞ := by
  norm_num [endpointCorrelatedBaseFixedConstant]

theorem endpointCorrelatedBaseThreshold_pos (absorbEta : Real) :
    0 < endpointCorrelatedBaseThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- Pure scalar closure of the crossed source-Frostman envelope.  Unlike a
standalone `CKT` power estimate, this is exactly the residual inequality
read by `sourceFrostman_crossedCardScale_to_eighthNormalized_baseBudget`.
-/
theorem crossedResidual_le_endpointThirdPower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {outputEta cardScaleEta thirdEta absorbEta : Real}
    (houtput : 0 <= outputEta) (hcard : 0 <= cardScaleEta)
    (hthird : 0 <= thirdEta) (habsorb : 0 < absorbEta)
    (hsmall : delta <= endpointCorrelatedBaseThreshold absorbEta)
    (hbudget :
      2 * outputEta + cardScaleEta + absorbEta <=
        (1 - P.epsilon) * thirdEta) :
    (480000 *
        (128 * (128 * (delta : ENNReal) ^ (-outputEta) *
          ((delta : ENNReal) ^ (-cardScaleEta)))) + 2) *
        2097152 * (delta : ENNReal) ^ (-outputEta) <=
      (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^
        (-thirdEta)) := by
  let d : ENNReal := (delta : ENNReal)
  let q : ENNReal := d ^ (-(outputEta + cardScaleEta))
  let K : ENNReal := endpointCorrelatedBaseFixedConstant
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d <= 1 := by
    change (delta : ENNReal) <= 1
    exact_mod_cast hD.delta_le_half.trans (by norm_num)
  have hqOne : 1 <= q := by
    by_cases hzero : outputEta + cardScaleEta = 0
    · simp only [q, hzero, neg_zero, ENNReal.rpow_zero, le_refl]
    · have hpos : 0 < outputEta + cardScaleEta :=
        lt_of_le_of_ne (add_nonneg houtput hcard) (Ne.symm hzero)
      exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
        (ENNReal.coe_pos.mpr hD.delta_pos) hdOne (by linarith)
  have hsourceCard :
      d ^ (-outputEta) * d ^ (-cardScaleEta) = q := by
    dsimp only [q]
    rw [show -(outputEta + cardScaleEta) =
        -outputEta + -cardScaleEta by ring,
      ENNReal.rpow_add _ _ hd0 hdTop]
  have hceiling :
      480000 * (128 * (128 * d ^ (-outputEta) *
          d ^ (-cardScaleEta))) + 2 <=
        (480000 * 128 * 128 + 2) * q := by
    calc
      480000 * (128 * (128 * d ^ (-outputEta) *
          d ^ (-cardScaleEta))) + 2 =
          480000 * 128 * 128 *
            (d ^ (-outputEta) * d ^ (-cardScaleEta)) + 2 := by ring
      _ = 480000 * 128 * 128 * q + 2 := by rw [hsourceCard]
      _ <= 480000 * 128 * 128 * q + 2 * q := by
        apply add_le_add le_rfl
        calc
          (2 : ENNReal) = 2 * 1 := by rw [mul_one]
          _ <= 2 * q := mul_le_mul' le_rfl hqOne
      _ = (480000 * 128 * 128 + 2) * q := by ring
  have hcoefficient : K <= d ^ (-absorbEta) := by
    dsimp only [K]
    exact finiteConstant_le_delta_negativePower
      endpointCorrelatedBaseFixedConstant_ne_top habsorb hD.delta_pos
        (by simpa only [endpointCorrelatedBaseThreshold] using hsmall)
  have hlhs :
      (480000 * (128 * (128 * d ^ (-outputEta) *
          d ^ (-cardScaleEta))) + 2) * 2097152 *
          d ^ (-outputEta) <=
        d ^ (-(2 * outputEta + cardScaleEta + absorbEta)) := by
    calc
      (480000 * (128 * (128 * d ^ (-outputEta) *
          d ^ (-cardScaleEta))) + 2) * 2097152 *
          d ^ (-outputEta) <=
        ((480000 * 128 * 128 + 2) * q) * 2097152 *
          d ^ (-outputEta) := mul_le_mul' (mul_le_mul' hceiling le_rfl) le_rfl
      _ = K * q * d ^ (-outputEta) := by
        simp only [K, endpointCorrelatedBaseFixedConstant]
        ring
      _ <= d ^ (-absorbEta) * q * d ^ (-outputEta) :=
        mul_le_mul' (mul_le_mul' hcoefficient le_rfl) le_rfl
      _ = d ^ (-(2 * outputEta + cardScaleEta + absorbEta)) := by
        dsimp only [q]
        rw [show -(2 * outputEta + cardScaleEta + absorbEta) =
            (-absorbEta + -(outputEta + cardScaleEta)) +
              -outputEta by ring,
          ENNReal.rpow_add _ _ hd0 hdTop,
          ENNReal.rpow_add _ _ hd0 hdTop]
  have hbudgetPower :
      d ^ (-(2 * outputEta + cardScaleEta + absorbEta)) <=
        d ^ (-((1 - P.epsilon) * thirdEta)) := by
    exact ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith)
  let rho := canonicalBufferedRadius W
  have hrho : rho = delta ^ (1 - P.epsilon) := by
    dsimp only [rho]
    exact endpointLongCore_canonicalBufferedRadius_eq_delta_rpow_one_sub
      (hD.delta_le_half.trans (by norm_num)) P W
  have hrhoPos : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hendpoint : d ^ (-((1 - P.epsilon) * thirdEta)) =
      (rho : ENNReal) ^ (-thirdEta) := by
    rw [hrho, ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne',
      <- ENNReal.rpow_mul]
    congr 1
    ring
  have heighth : (rho : ENNReal) ^ (-thirdEta) <=
      (((rho / 8 : NNReal) : ENNReal) ^ (-thirdEta)) := by
    rw [<- ENNReal.coe_rpow_of_ne_zero hrhoPos.ne' (-thirdEta),
      <- ENNReal.coe_rpow_of_ne_zero
        (div_pos hrhoPos (by norm_num : (0 : NNReal) < 8)).ne'
        (-thirdEta)]
    exact ENNReal.coe_le_coe.mpr
      (NNReal.rpow_le_rpow_of_nonpos
        (div_pos hrhoPos (by norm_num : (0 : NNReal) < 8))
        (div_le_self (show 0 <= rho from bot_le) (by norm_num))
        (neg_nonpos.mpr hthird))
  simpa only [d, rho] using
    hlhs.trans (hbudgetPower.trans (hendpoint.le.trans heighth))


/-- Internal scalar projection of the same crossed envelope used by the full
B2 base product.  This is not a standalone Katz--Tao premise: the literal CKT
coefficient is bounded only after its source-volume cancellation is combined
with the power bound for the card-scale mass on this same cover. -/
theorem endpointIdentity_correlated_recomputedThird_scalarBase
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {outputEta cardScaleEta thirdEta absorbEta : Real}
    (houtput : 0 <= outputEta) (hcard : 0 <= cardScaleEta)
    (hthird : 0 <= thirdEta) (habsorb : 0 < absorbEta)
    (hXPower :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let C := identityRadiusCoherentCover E.family
      let S := endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))
      let U0 := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      let U := activeFineRestrictedScaleCover U0
      (activeCoarseCardScaleMass U : ENNReal) <=
        (delta : ENNReal) ^ (-cardScaleEta))
    (hsmall : delta <= endpointCorrelatedBaseThreshold absorbEta)
    (hbudget :
      2 * outputEta + cardScaleEta + absorbEta <=
        (1 - P.epsilon) * thirdEta) :
    let rho := canonicalBufferedRadius W
    let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    ((conflictThreshold + 1 : Nat) : ENNReal) * 2097152 *
        (delta : ENNReal) ^ (-outputEta) <=
      (((rho / 8 : NNReal) : ENNReal) ^ (-thirdEta)) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let X : ENNReal := activeCoarseCardScaleMass U0
  let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
  let dPower : ENNReal := (delta : ENNReal) ^ (-outputEta)
  let XUpper : ENNReal := (delta : ENNReal) ^ (-cardScaleEta)
  let L : ENNReal :=
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
      ENNReal)
  let B : ENNReal :=
    480000 * (128 * (128 * dPower * XUpper)) + 2
  have hrhoPos : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hscale : S.tau W.m <= rho := by
    dsimp only [rho]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  have hdeltaRho : delta <= rho := (S.delta_le_tau W.m).trans hscale
  have hCfinite : CKT ≠ ∞ := by
    dsimp only [CKT, rho]
    exact identitySourceFrostmanKatzTaoConstant_ne_top
      D (canonicalBufferedRadius W) hD.delta_pos outputEta
  let G := canonicalBufferedGlobalCover W hE.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hglobalIdentity : G =
      identityRadiusScaleCover E.family rho hdeltaRho := by
    simpa only [G, rho, C, S] using
      identityCore_canonicalBufferedGlobalCover_eq_identityRadiusScaleCover
        E hE S P W hepsilonHalf
  have hcardScaleU0G :
      (activeCoarseCardScaleMass U0 : ENNReal) =
        (activeCoarseCardScaleMass G : ENNReal) := by rfl
  have hCglobal :=
    identitySourceFrostmanKatzTaoConstant_mul_unitBallVolume_le_cardScale
      D hD rho hdeltaRho (eta := outputEta)
  rw [<- hglobalIdentity, <- hcardScaleU0G] at hCglobal
  have hXUpper : X <= XUpper := by
    have hrestricted : activeCoarseCardScaleMass U =
        activeCoarseCardScaleMass U0 := by
      simp only [U, activeCoarseCardScaleMass,
        activeFineRestrictedScaleCover, Finset.card_univ,
        Fintype.card_fin]
    change (activeCoarseCardScaleMass U0 : ENNReal) <=
      (delta : ENNReal) ^ (-cardScaleEta)
    rw [<- hrestricted]
    simpa only [E, hE, C, S, U0, U, X, XUpper] using hXPower
  have hunitOne : (1 : ENNReal) <=
      volume (unitBallBody : Set Space) := by
    rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
    norm_num
    nlinarith [Real.pi_gt_three]
  have hCKTUpper : CKT <= 128 * dPower * XUpper := by
    calc
      CKT = CKT * 1 := by rw [mul_one]
      _ <= CKT * volume (unitBallBody : Set Space) :=
        mul_le_mul' le_rfl hunitOne
      _ <= 128 * dPower * X := by
        simpa only [CKT, X, dPower] using hCglobal
      _ <= 128 * dPower * XUpper := mul_le_mul' le_rfl hXUpper
  have hscaledFinite : (128 : ENNReal) * CKT ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCfinite
  have hL : L <= B := by
    calc
      L <= 480000 * (128 * CKT) + 2 := by
        dsimp only [L]
        exact fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
      _ <= 480000 * (128 * (128 * dPower * XUpper)) + 2 := by
        gcongr
  have hresidual := crossedResidual_le_endpointThirdPower
    D hD P W houtput hcard hthird habsorb hsmall hbudget
  calc
    L * 2097152 * dPower <= B * 2097152 * dPower :=
      mul_le_mul' (mul_le_mul' hL le_rfl) le_rfl
    _ <= (((rho / 8 : NNReal) : ENNReal) ^ (-thirdEta)) := by
      simpa only [B, dPower, XUpper, rho] using hresidual

/-- The complete base inequality for the one literal endpoint cover.  This
is the exact field consumed by the recomputed-neighborhood B2/Frostman
constructor.  The only non-geometric premise is an upper power for the
literal card-scale mass `X` on this same cover. -/
theorem endpointIdentity_correlated_recomputedThird_baseBudget
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {outputEta cardScaleEta thirdEta absorbEta : Real}
    (houtput : 0 <= outputEta) (hcard : 0 <= cardScaleEta)
    (hthird : 0 <= thirdEta) (habsorb : 0 < absorbEta)
    (hXPower :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let C := identityRadiusCoherentCover E.family
      let S := endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))
      let U0 := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      let U := activeFineRestrictedScaleCover U0
      (activeCoarseCardScaleMass U : ENNReal) <=
        (delta : ENNReal) ^ (-cardScaleEta))
    (hsmall : delta <= endpointCorrelatedBaseThreshold absorbEta)
    (hbudget :
      2 * outputEta + cardScaleEta + absorbEta <=
        (1 - P.epsilon) * thirdEta) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let rho := canonicalBufferedRadius W
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    ((conflictThreshold + 1 : Nat) : ENNReal) *
        ((128 * CKT) * volume (unitBallBody : Set Space)) <=
      (((rho / 8 : NNReal) : ENNReal) ^ (-thirdEta)) *
        ((Fintype.card (Fin U.coarseCard) : ENNReal) *
          ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2)) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let X : ENNReal := activeCoarseCardScaleMass U0
  let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
  have hrhoPos : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hscale : S.tau W.m <= rho := by
    dsimp only [rho]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  have hdeltaRho : delta <= rho := (S.delta_le_tau W.m).trans hscale
  have hCfinite : CKT ≠ ∞ := by
    dsimp only [CKT, rho]
    exact identitySourceFrostmanKatzTaoConstant_ne_top
      D (canonicalBufferedRadius W) hD.delta_pos outputEta
  let G := canonicalBufferedGlobalCover W hE.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hglobalIdentity : G =
      identityRadiusScaleCover E.family rho hdeltaRho := by
    simpa only [G, rho, C, S] using
      identityCore_canonicalBufferedGlobalCover_eq_identityRadiusScaleCover
        E hE S P W hepsilonHalf
  have hcardScaleU0G :
      (activeCoarseCardScaleMass U0 : ENNReal) =
        (activeCoarseCardScaleMass G : ENNReal) := by rfl
  have hCglobal :=
    identitySourceFrostmanKatzTaoConstant_mul_unitBallVolume_le_cardScale
      D hD rho hdeltaRho (eta := outputEta)
  rw [<- hglobalIdentity, <- hcardScaleU0G] at hCglobal
  have hXIdentity := activeCoarseCardScaleMass_eq_restricted_coarse_card U0
  have hX : X =
      (Fintype.card (Fin U.coarseCard) : ENNReal) *
        (rho : ENNReal) ^ 2 := by
    simpa only [X, U] using hXIdentity
  have hXUpper : X <= (delta : ENNReal) ^ (-cardScaleEta) := by
    have hrestricted : activeCoarseCardScaleMass U =
        activeCoarseCardScaleMass U0 := by
      simp only [U, activeCoarseCardScaleMass,
        activeFineRestrictedScaleCover, Finset.card_univ,
        Fintype.card_fin]
    change (activeCoarseCardScaleMass U0 : ENNReal) <=
      (delta : ENNReal) ^ (-cardScaleEta)
    rw [<- hrestricted]
    simpa only [E, hE, C, S, U0, U, X] using hXPower
  have hresidual := crossedResidual_le_endpointThirdPower
    D hD P W houtput hcard hthird habsorb hsmall hbudget
  have hbase :=
    sourceFrostman_crossedCardScale_to_eighthNormalized_baseBudget
      (delta := delta) (rho := rho) (CKT := CKT) (X := X)
      (XUpper := (delta : ENNReal) ^ (-cardScaleEta))
      (card := Fintype.card (Fin U.coarseCard))
      (etaSource := outputEta) (etaThird := thirdEta)
      hCfinite hX
      (by simpa only [CKT, X] using hCglobal)
      hXUpper hresidual
  simpa only [CKT, rho, U] using hbase

#print axioms endpointCorrelatedBaseThreshold_pos
#print axioms crossedResidual_le_endpointThirdPower
#print axioms endpointIdentity_correlated_recomputedThird_baseBudget

end
end Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1
