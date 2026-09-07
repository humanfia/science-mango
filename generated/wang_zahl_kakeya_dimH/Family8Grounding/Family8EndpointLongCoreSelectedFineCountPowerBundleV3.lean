import Family8Grounding.Family8NormalizedLongCoreDoubledFiberCountLossPowerV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveBasicTransportsV2
import Family8Grounding.Family8SelectedFineEndpointCountComparisonV1
import Family8Grounding.Family8StickyKatzTaoBoundedFiberPartitionV4
import Mathlib.Tactic

/-!
# Endpoint long-core selected-fibre count and power bundle, V3

For the literal endpoint identity interval, this adapter keeps one explicit
selected-fibre witness throughout.  Its three count factors satisfy the
required comparison with the honest doubled-fibre cap, and that same cap has
the canonical source-delta power bound.  V1 and V2 are failed elaboration
drafts and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped ENNReal NNReal

namespace Family8EndpointLongCoreSelectedFineCountPowerBundleV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointLongCoreIdentityIntervalCountsV3
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreDoubledFiberCountLossPowerV1
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8ParameterLadderV1
open Family8SelectedFineEndpointCountComparisonV1
open Family8StickyKatzTaoBoundedFiberPartitionV4
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

/-- On one literal selected-fibre witness, the endpoint count comparison and
the source-delta power estimate use definitionally the same natural cap. -/
theorem endpointLongCore_selectedFine_countComparison_and_power
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
    {CKT : ENNReal} {etaKT absorbEta : Real}
    (hCKTfinite : CKT ≠ ∞)
    (hCKTone : 1 <= CKT)
    (hKTEvery :
      (identityRadiusCoherentCover
        (fullRefinementDatum D).family).base.IsKatzTaoAtEveryScale CKT)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (habsorbEta : 0 < absorbEta)
    (hdeltaFiber : delta <=
      Family8LongIntervalOrdinaryFiberCapNumericsV1.ordinaryFiberNatCapSmallDeltaThreshold
        absorbEta) :
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
          (M : ENNReal) <=
            (delta : ENNReal) ^
              (-Family8LongIntervalOrdinaryFiberCapNumericsV1.ordinaryFiberPowerEnvelope
                P.epsilon etaKT absorbEta) := by
  dsimp only
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
  intro selectedFine hselectedFine q picked
  have htauHalf : S.tau W.m <= (2 : NNReal)⁻¹ :=
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
      (hbufferedSixteenth.trans (by
        change (1 : Real) / 16 <= (2 : Real)⁻¹
        norm_num))
  have hbOne : canonicalBufferedRadius W <= 1 :=
    hbufferedSixteenth.trans (by
      change (1 : Real) / 16 <= (1 : Real)
      norm_num)
  have hKTtau : IsKatzTao CKT
      (tauActiveCoarseDatum E C S W).family.bodyFamily :=
    tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
      E C S P W
        (hKTEvery (S.tau W.m) (S.delta_le_tau W.m)
          ((S.tau_le_theta W.m).trans (S.theta_le_one W.m)))
  have hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      U0 (hD.delta_pos.trans_le (S.delta_le_tau W.m))
        htauHalf hbOne hCKTfinite hKTtau
  have hcoarseCard : U.coarseCard = Fintype.card index :=
    endpointLongCore_activeFineRestricted_coarseCard_eq_indexCard
      D hD P W hepsilonHalf
  constructor
  · exact selectedFine_endpoint_countComparison
      U selectedFine hselectedFine q picked M hM hcoarseCard
  · exact canonicalBuffered_doubledFiberCountLoss_le_power
      E hE C S P W hCKTone hCKT habsorbEta hdeltaFiber

#print axioms endpointLongCore_selectedFine_countComparison_and_power

end
end Family8EndpointLongCoreSelectedFineCountPowerBundleV3
