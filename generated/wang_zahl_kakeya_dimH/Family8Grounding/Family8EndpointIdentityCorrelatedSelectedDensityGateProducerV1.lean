import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1
import Family8Grounding.Family8EndpointLongCoreIdentityTauActiveDensitySquareV4
import Family8Grounding.Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3
import Family8Grounding.Family8IdentityExactOuterDensityBudgetPowerV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1
import Mathlib.Tactic

/-!
# Correlated selected-exponent density gate

The selected high-gamma route keeps the literal endpoint card-scale mass
correlated with the source Katz--Tao constant.  This file spends that one
same-cover power bound directly in the normalized density gate.  In
particular, it does not expose a standalone Katz--Tao power estimate.

The exponent ledger is

`3 * outputEta + cardScaleEta + 2 * absorbEta <=
  (1 - P.epsilon) * thirdEta`.

The card-scale exponent is deliberately arbitrary: the upstream selected
card-scale producer may choose any exponent fitting this ledger.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityCorrelatedSelectedDensityGateProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1
open Family8EndpointIdentityLongCoreSourceKatzTaoBudgetV1
open Family8EndpointLongCoreIdentityTauActiveDensitySquareV4
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8IdentityCoreCanonicalBufferedLossOneAdapterV1
open Family8IdentityExactOuterDensityBudgetPowerV2
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The fixed coefficient in the correlated density gate is strictly smaller
than the already allocated correlated-base coefficient. -/
theorem correlatedSelectedDensityFixedConstant_le_base :
    ((480000 * 128 * 128 + 2 : ENNReal) * 128 * 768) <=
      endpointCorrelatedBaseFixedConstant := by
  norm_num [endpointCorrelatedBaseFixedConstant]

/-- The conflict ceiling, its normalization, and the actual frozen loss are
paid from a correlated source/card-scale estimate. -/
theorem correlatedSelectedDensityCoefficient_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {CKT : ENNReal}
    {outputEta cardScaleEta absorbEta : Real}
    (houtput : 0 < outputEta) (hcard : 0 <= cardScaleEta)
    (habsorb : 0 < absorbEta)
    (hCKTfinite : CKT ≠ ∞)
    (hCKT : CKT <=
      128 * (delta : ENNReal) ^ (-outputEta) *
        (delta : ENNReal) ^ (-cardScaleEta))
    (hsmall : delta <= endpointCorrelatedBaseThreshold absorbEta) :
    (128 *
          ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
            ENNReal)) *
        ((delta : ENNReal) ^ (-absorbEta) * 768) <=
      (delta : ENNReal) ^
        (-(outputEta + cardScaleEta + 2 * absorbEta)) := by
  let d : ENNReal := (delta : ENNReal)
  let a : Real := outputEta + cardScaleEta
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d <= 1 := by
    change (delta : ENNReal) <= 1
    exact_mod_cast hD.delta_le_half.trans (by norm_num)
  have ha : 0 < a := by
    dsimp only [a]
    exact add_pos_of_pos_of_nonneg houtput hcard
  have haOne : 1 <= d ^ (-a) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.coe_pos.mpr hD.delta_pos) hdOne (neg_lt_zero.mpr ha)
  have hsourcePower :
      d ^ (-outputEta) * d ^ (-cardScaleEta) = d ^ (-a) := by
    rw [show -a = -outputEta + -cardScaleEta by
      dsimp only [a]
      ring, ENNReal.rpow_add _ _ hd0 hdTop]
  have hCKT' : CKT <= 128 * d ^ (-a) := by
    calc
      CKT <= 128 * d ^ (-outputEta) * d ^ (-cardScaleEta) := by
        simpa only [d] using hCKT
      _ = 128 * (d ^ (-outputEta) * d ^ (-cardScaleEta)) := by ring
      _ = 128 * d ^ (-a) := by rw [hsourcePower]
  have hscaledFinite : (128 : ENNReal) * CKT ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCKTfinite
  have hclosed :
      ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) <=
        480000 * (128 * CKT) + 2 :=
    fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
  have hceiling :
      ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) <=
        (480000 * 128 * 128 + 2) * d ^ (-a) := by
    calc
      ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) <= 480000 * (128 * CKT) + 2 := hclosed
      _ <= 480000 * (128 * (128 * d ^ (-a))) + 2 := by
        gcongr
      _ = (480000 * 128 * 128) * d ^ (-a) + 2 := by ring
      _ <= (480000 * 128 * 128) * d ^ (-a) + 2 * d ^ (-a) := by
        apply add_le_add le_rfl
        calc
          (2 : ENNReal) = 2 * 1 := by rw [mul_one]
          _ <= 2 * d ^ (-a) := mul_le_mul' le_rfl haOne
      _ = (480000 * 128 * 128 + 2) * d ^ (-a) := by ring
  have hbaseConstant : endpointCorrelatedBaseFixedConstant <=
      d ^ (-absorbEta) := by
    exact finiteConstant_le_delta_negativePower
      endpointCorrelatedBaseFixedConstant_ne_top habsorb hD.delta_pos
        (by simpa only [endpointCorrelatedBaseThreshold, d] using hsmall)
  have hcombine :
      d ^ (-absorbEta) * d ^ (-a) * d ^ (-absorbEta) =
        d ^ (-(a + 2 * absorbEta)) := by
    rw [<- ENNReal.rpow_add _ _ hd0 hdTop,
      <- ENNReal.rpow_add _ _ hd0 hdTop]
    congr 1
    ring
  calc
    (128 *
          ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
            ENNReal)) *
        (d ^ (-absorbEta) * 768) <=
      (128 * ((480000 * 128 * 128 + 2) * d ^ (-a))) *
        (d ^ (-absorbEta) * 768) := mul_le_mul' (mul_le_mul' le_rfl hceiling) le_rfl
    _ = ((480000 * 128 * 128 + 2 : ENNReal) * 128 * 768) *
        d ^ (-a) * d ^ (-absorbEta) := by ring
    _ <= endpointCorrelatedBaseFixedConstant *
        d ^ (-a) * d ^ (-absorbEta) := by
      gcongr
      exact correlatedSelectedDensityFixedConstant_le_base
    _ <= d ^ (-absorbEta) * d ^ (-a) * d ^ (-absorbEta) := by
      gcongr
    _ = d ^ (-(a + 2 * absorbEta)) := hcombine
    _ = (delta : ENNReal) ^
        (-(outputEta + cardScaleEta + 2 * absorbEta)) := by
      simp only [d, a]

/-- The full assembly-independent scalar density budget on the one literal
endpoint cover.  Its only analytic input is the card-scale mass power on
that same cover. -/
theorem endpointIdentity_correlatedSelected_densityPower
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
    (houtput : 0 < outputEta) (hcard : 0 <= cardScaleEta)
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
    (hsmallBase : delta <= endpointCorrelatedBaseThreshold absorbEta)
    (hbudget :
      3 * outputEta + cardScaleEta + 2 * absorbEta <=
        (1 - P.epsilon) * thirdEta) :
    let rho := canonicalBufferedRadius W
    let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    ((((rho / 8 : NNReal) : ENNReal) ^ thirdEta *
        (128 * ((conflictThreshold + 1 : Nat) : ENNReal))) *
        ((delta : ENNReal) ^ (-absorbEta) * 768) <=
      (delta : ENNReal) ^ (2 * outputEta)) := by
  dsimp only at hXPower ⊢
  let d : ENNReal := (delta : ENNReal)
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
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d <= 1 := by
    change (delta : ENNReal) <= 1
    exact_mod_cast hD.delta_le_half.trans (by norm_num)
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
  have hXUpper : X <= d ^ (-cardScaleEta) := by
    have hrestricted : activeCoarseCardScaleMass U =
        activeCoarseCardScaleMass U0 := by
      simp only [U, activeCoarseCardScaleMass,
        activeFineRestrictedScaleCover, Finset.card_univ,
        Fintype.card_fin]
    change (activeCoarseCardScaleMass U0 : ENNReal) <=
      (delta : ENNReal) ^ (-cardScaleEta)
    rw [<- hrestricted]
    simpa only [E, hE, C, S, U0, U, X, d] using hXPower
  have hCKT : CKT <=
      128 * d ^ (-outputEta) * d ^ (-cardScaleEta) := by
    calc
      CKT = CKT * 1 := by rw [mul_one]
      _ <= CKT * volume (unitBallBody : Set Space) :=
        mul_le_mul' le_rfl one_le_volume_unitBallBody
      _ <= 128 * d ^ (-outputEta) * X := by
        simpa only [CKT, X, d] using hCglobal
      _ <= 128 * d ^ (-outputEta) * d ^ (-cardScaleEta) := by
        gcongr
  have hcoefficient := correlatedSelectedDensityCoefficient_le_power
    D hD houtput hcard habsorb hCfinite hCKT hsmallBase
  have heighth :
      (((rho / 8 : NNReal) : ENNReal) ^ thirdEta) <=
        (rho : ENNReal) ^ thirdEta := by
    apply ENNReal.rpow_le_rpow
    · exact ENNReal.coe_le_coe.mpr
        (div_le_self (show 0 <= rho from bot_le) (by norm_num))
    · exact hthird
  have hrho : rho = delta ^ (1 - P.epsilon) := by
    dsimp only [rho]
    exact endpointLongCore_canonicalBufferedRadius_eq_delta_rpow_one_sub
      (hD.delta_le_half.trans (by norm_num)) P W
  have hrhoPower :
      (rho : ENNReal) ^ thirdEta =
        d ^ ((1 - P.epsilon) * thirdEta) := by
    rw [hrho, ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne',
      <- ENNReal.rpow_mul]
  have hcombine :
      d ^ ((1 - P.epsilon) * thirdEta) *
          d ^ (-(outputEta + cardScaleEta + 2 * absorbEta)) =
        d ^ ((1 - P.epsilon) * thirdEta -
          (outputEta + cardScaleEta + 2 * absorbEta)) := by
    rw [<- ENNReal.rpow_add _ _ hd0 hdTop]
    congr 1
  have hlhs :
      (((rho / 8 : NNReal) : ENNReal) ^ thirdEta *
          (128 *
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal))) *
          (d ^ (-absorbEta) * 768) <=
        d ^ (2 * outputEta) := by
    calc
      (((rho / 8 : NNReal) : ENNReal) ^ thirdEta *
          (128 *
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal))) *
          (d ^ (-absorbEta) * 768) =
        (((rho / 8 : NNReal) : ENNReal) ^ thirdEta) *
          ((128 *
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal)) * (d ^ (-absorbEta) * 768)) := by ac_rfl
      _ <= (rho : ENNReal) ^ thirdEta *
          d ^ (-(outputEta + cardScaleEta + 2 * absorbEta)) :=
        mul_le_mul' heighth hcoefficient
      _ = d ^ ((1 - P.epsilon) * thirdEta) *
          d ^ (-(outputEta + cardScaleEta + 2 * absorbEta)) := by
        rw [hrhoPower]
      _ = d ^ ((1 - P.epsilon) * thirdEta -
          (outputEta + cardScaleEta + 2 * absorbEta)) := hcombine
      _ <= d ^ (2 * outputEta) := by
        apply ENNReal.rpow_le_rpow_of_exponent_ge hdOne
        linarith
  simpa only [rho, CKT, d] using hlhs

/-- Assembly-local form of the density gate.  The frozen-coarse identity is
not needed for this inequality; only the literal actual loss is used. -/
private theorem endpointIdentity_correlatedSelected_densityGate_forall
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
    (houtput : 0 < outputEta) (hcard : 0 <= cardScaleEta)
    (hthird : 0 <= thirdEta) (habsorb : 0 < absorbEta)
    (hFOutput : FrostmanHypotheses D outputEta)
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
    (hsmallBase : delta <= endpointCorrelatedBaseThreshold absorbEta)
    (hsmallFrozen : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        absorbEta)
    (hbudget :
      3 * outputEta + cardScaleEta + 2 * absorbEta <=
        (1 - P.epsilon) * thirdEta) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let rho := canonicalBufferedRadius W
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
      have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
        rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
          D hD P W hepsilonHalf]
        have hfloor :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFOutput
        exact ne_of_gt ((ENNReal.rpow_pos
          (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
      rw [shadingMass_restrictTo_eq_sum]
      exact hOn
    let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
      intro k _hk
      simpa only [Fintype.card_coe] using
        identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
          E hE S W P.epsilon_pos.le hepsilonHalf k
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse 1 hM
    let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    forall A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) ->
      (((rho / 8 : NNReal) : ENNReal) ^ thirdEta *
          (128 * ((conflictThreshold + 1 : Nat) : ENNReal)) <=
        Y.shadingDensity ^ 2 /
          ((A.loss : ENNReal) *
            (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2))) := by
  have hpower := endpointIdentity_correlatedSelected_densityPower
    D hD P W hepsilonHalf houtput hcard hthird habsorb
      hXPower hsmallBase hbudget
  dsimp only at hpower ⊢
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
    rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
      D hD P W hepsilonHalf]
    have hfloor :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFOutput
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 := by
    rw [shadingMass_restrictTo_eq_sum]
    exact hOn
  have hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
    intro k _hk
    simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le hepsilonHalf k
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  have hscale : S.tau W.m <= rho := by
    dsimp only [rho]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  let Pcoarse := boundedFiberCoarseTubePartition U hscale hcoarse 1 hM
  let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
  let conflictThreshold :=
    Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
  intro A hAloss
  have hbranchingLoss : Pcoarse.branchingLoss = 1 :=
    boundedFiberCoarseTubePartition_branchingLoss
      U hscale hcoarse 1 hM
  have hdensity :
      (delta : ENNReal) ^ (2 * outputEta) <=
        Y.shadingDensity ^ 2 := by
    simpa only [E, hE, C, S, U0, Dtau, Y] using
      endpointLongCore_identity_canonicalBufferedTauActive_density_sq_lower
        D hD P W hepsilonHalf hFOutput
  have hLossRaw :=
    canonicalBufferedTauActive_frozenLoss_le_power
      E hE C S P W hepsilonHalf habsorb hsmallFrozen
  have hLoss : (A.loss : ENNReal) <=
      (delta : ENNReal) ^ (-absorbEta) := by
    rw [hAloss]
    exact hLossRaw
  have hactualPos : 0 < A.loss := by
    rw [hAloss]
    unfold frozenComparableLoss
    positivity
  have hactual0 : (A.loss : ENNReal) ≠ 0 := by
    exact_mod_cast hactualPos.ne'
  have hactualTop : (A.loss : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hgate := target_le_density_div_actualLoss_mul_768
    hactual0 hactualTop hLoss hdensity
      (by simpa only [rho, CKT, conflictThreshold] using hpower)
  change (((rho / 8 : NNReal) : ENNReal) ^ thirdEta *
      (128 * ((conflictThreshold + 1 : Nat) : ENNReal)) <=
    Y.shadingDensity ^ 2 /
      ((A.loss : ENNReal) *
        (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2)))
  simpa only [Pcoarse, hbranchingLoss, Nat.cast_one, one_pow, mul_one] using hgate

/-- Exact selected-assembly density premise consumed by the correlated DSO.
The assembly and both of its literal identities are produced here; neither
the selected assembly nor a nonzero-mass hypothesis is an input. -/
theorem exists_endpointIdentity_correlatedSelected_densityAssembly
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
    (houtput : 0 < outputEta) (hcard : 0 <= cardScaleEta)
    (hthird : 0 <= thirdEta) (habsorb : 0 < absorbEta)
    (hFOutput : FrostmanHypotheses D outputEta)
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
    (hsmallBase : delta <= endpointCorrelatedBaseThreshold absorbEta)
    (hsmallFrozen : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        absorbEta)
    (hbudget :
      3 * outputEta + cardScaleEta + 2 * absorbEta <=
        (1 - P.epsilon) * thirdEta) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let rho := canonicalBufferedRadius W
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
      have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
        rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
          D hD P W hepsilonHalf]
        have hfloor :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFOutput
        exact ne_of_gt ((ENNReal.rpow_pos
          (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
      rw [shadingMass_restrictTo_eq_sum]
      exact hOn
    let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
      intro k _hk
      simpa only [Fintype.card_coe] using
        identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
          E hE S W P.epsilon_pos.le hepsilonHalf k
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse 1 hM
    let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) /\
      A.frozenCoarse =
          Pcoarse.asConvexFactorization.inducedShading
            A.refinement.shading /\
      (((rho / 8 : NNReal) : ENNReal) ^ thirdEta *
          (128 * ((conflictThreshold + 1 : Nat) : ENNReal)) <=
        Y.shadingDensity ^ 2 /
          ((A.loss : ENNReal) *
            (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2))) := by
  dsimp only at hXPower ⊢
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFOutput
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
  have hAssembly :=
    exists_endpointLongCore_canonicalBufferedTauActive_singletonExactOuterAssembly
      D hD P W hepsilonHalf hmass
  dsimp only at hAssembly
  obtain ⟨_hbranchLoss, _hbranch, A, hAloss, hfrozen,
      _k, _hk, _hpositive⟩ := hAssembly
  have hforall := endpointIdentity_correlatedSelected_densityGate_forall
    D hD P W hepsilonHalf houtput hcard hthird habsorb hFOutput
      (by simpa only [E, hE, C, S, U0, U] using hXPower)
      hsmallBase hsmallFrozen hbudget
  dsimp only at hforall
  refine ⟨A, hAloss, hfrozen, ?_⟩
  exact hforall A hAloss

#print axioms correlatedSelectedDensityFixedConstant_le_base
#print axioms correlatedSelectedDensityCoefficient_le_power
#print axioms endpointIdentity_correlatedSelected_densityPower
#print axioms exists_endpointIdentity_correlatedSelected_densityAssembly

end
end Family8EndpointIdentityCorrelatedSelectedDensityGateProducerV1
