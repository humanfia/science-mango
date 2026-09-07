import Family8Grounding.Family8EndpointLongCoreIdentityFirstAggregatePowerV1
import Family8Grounding.Family8EndpointLongCoreSelectedFineCountPowerBundleV3
import Mathlib.Tactic

/-!
# Endpoint selected-fibre count and aggregate-loss bundle, V2

This final count-side adapter keeps one selected-fibre witness from the
literal count comparison through the aggregate loss.  V1 is a failed
namespace draft and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

open Set
open scoped ENNReal NNReal

namespace Family8EndpointLongCoreSelectedFineCountAggregateBundleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointLongCoreIdentityFirstAggregatePowerV1
open Family8EndpointLongCoreSelectedFineCountPowerBundleV3
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8ParameterLadderV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickySelectedFineSubtypeScaleCoverV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The exact `hCount` and `hAggregateLoss` fields for one endpoint selected
fibre.  The automatic natural-cap power is consumed internally. -/
theorem endpointLongCore_selectedFine_count_and_aggregate_fields
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {CKT : ENNReal} {etaKT absorbEta thirdExponent : Real}
    (hCKTfinite : CKT ≠ ∞)
    (hCKTone : 1 <= CKT)
    (hKTEvery :
      (identityRadiusCoherentCover
        (fullRefinementDatum D).family).base.IsKatzTaoAtEveryScale CKT)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (habsorbEta : 0 < absorbEta)
    (hdeltaFiber : delta <=
      Family8LongIntervalOrdinaryFiberCapNumericsV1.ordinaryFiberNatCapSmallDeltaThreshold
        absorbEta)
    (hgammaTwo : gamma <= 2)
    (thirdLoss : ENNReal)
    (hThirdPower : thirdLoss <=
      (delta : ENNReal) ^ (-thirdExponent))
    (hExponentBudget :
      thirdExponent +
          Family8LongIntervalOrdinaryFiberCapNumericsV1.ordinaryFiberPowerEnvelope
            P.epsilon etaKT absorbEta * (1 - gamma / 2) <=
        3 * P.eta W.stage) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    let M := katzTaoDoubledFiberNatCap
      (S.tau W.m) (canonicalBufferedRadius W) CKT
    forall (selectedFine : Finset {i // i ∈ U0.activeFine})
      (hselectedFine : selectedFine ⊆ U.activeFine),
      forall q : Fin (selectedFineParentValues U selectedFine).card,
        forall picked : Finset {i // i ∈
          (selectedFineScaleCover U selectedFine hselectedFine).fiber q},
          (((1 * (picked.card * Fintype.card (Fin U.coarseCard)) : Nat) :
              ENNReal)) <=
                (M : ENNReal) * (Fintype.card index : ENNReal) /\
          ((1 * thirdLoss) * (M : ENNReal) ^ (1 - gamma / 2)) <=
            (delta : ENNReal) ^ (-3 * P.eta W.stage) := by
  dsimp only
  intro selectedFine hselectedFine q picked
  obtain ⟨hCount, hCountPower⟩ :=
    endpointLongCore_selectedFine_countComparison_and_power
      D hD P W hepsilonHalf hbufferedSixteenth hCKTfinite hCKTone
        hKTEvery hCKT habsorbEta hdeltaFiber
          selectedFine hselectedFine q picked
  refine ⟨hCount, ?_⟩
  exact identityFirst_thirdCountAggregateLoss_le_threeEta
    hD.delta_pos (hD.delta_le_half.trans (by norm_num)) hgammaTwo
      hThirdPower hCountPower hExponentBudget

#print axioms endpointLongCore_selectedFine_count_and_aggregate_fields

end
end Family8EndpointLongCoreSelectedFineCountAggregateBundleV2
