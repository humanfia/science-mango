import Family8Grounding.Family8WinnerSideJointBucketEndpointPackedEq32ConsumerV1
import Family8Grounding.Family8WinnerSideJointBucketEndpointPackedEq32LossPowerV1
import Family8Grounding.Family8EndpointIdentitySameCoreHighLossAwareEq32IntegrationV1
import Family8Grounding.Family8SelectedOccurrenceFineBucketSupportV1
import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV1
import Mathlib.Tactic

/-!
# Winner-side packed Equation (32) into the loss-aware endpoint

This is the thin fixed-witness adapter between the green winner-side
Equation-(32) consumer and `EndpointIdentityLossAwareEq32PaymentAt`.

The joint bucket, winner-side bucket, frozen source-average retention, and
the packed consumer's finite/logarithmic coefficient are paid by the exact
automatic loss-power theorem.  There are two distinct occurrences of the
frozen-comparable loss: one transports the retained source average to the
chosen refinement, while the one already inside the packed loss pays the
positive-carrier/source-density comparison.

The outer coefficient comparison, Equation-(45) estimate, and joint-scale
geometric estimate remain literal hypotheses at the already chosen assembly,
occurrence, and inner label.  The only final scalar hypothesis is the
displayed Section-Eight power budget with
`outerLoss * geometryLoss * coefficientLoss ^ (1 - gamma / 2)` left visible. At the terminal
we choose `countLoss = 1`: the consumer has already paid its internal count
comparison `2` through `2 ^ (1 - gamma / 2)`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8WinnerSideJointBucketEndpointPackedEq32LossAwarePaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8OuterInnerMismatchHighGammaPackingBridgeV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFineBucketSupportV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1
open Family8SelectedOccurrenceWeightedWinnerSideBucketV1
open Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
open Family8SelectedParentAngleBucketLogarithmicLossV2
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentSideHullReserveProducerV1
open Family8SameScaleActiveParentActualDatumAdmissibilityV1
open Family8SourceActiveFineActualAverageIdentityV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8WinnerSideJointBucketEndpointPackedEq32ConsumerV1
open Family8WinnerSideJointBucketEndpointPackedEq32LossPowerV1
open Family8EndpointIdentitySameCoreHighLossAwareEq32IntegrationV1
open Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
open Family8FullRefinementActualDatumV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66ASectionEightCollapsedAlgebraV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The three genuinely external analytic estimates, stated only at the
assembly, occurrence, and inner label already chosen by the automatic
winner-side payment. -/
def WinnerSideEndpointPackedChosenOuterCoefficientGeometryBudget
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family delta)
    (hdelta : 0 < delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (W : WinnerSideEq32ChosenWitness D S hdelta P R Y fineBucket
      rFrozen r hr)
    (base : ENNReal) (bucketKey : Nat)
    (outerCFUsed coefficientLoss sourceCF : ENNReal)
    (outerLoss refinementLoss geometryLoss : ENNReal)
    (epsilon gamma : Real) : Prop :=
  outerCFUsed <= coefficientLoss * sourceCF *
        ((2 : ENNReal) ^ bucketKey * base)⁻¹ /\
    W.payment.assembly.frozenCoarse.averageMultiplicity <=
      outerLoss * proposition66AOuterFactor delta
        (bucketShortA W.outerLabel) (bucketShortB W.outerLabel)
        (winnerSideRetainedOccurrences D S P hdelta R W.outerLabel).card
        (outerCFUsed * refinementLoss) epsilon gamma /\
    winnerSideEndpointJohnLoss *
        ((((2 : ENNReal) ^ (gamma / 2) *
              (selectedParentSideHullEnvelope delta
                (bucketShortA W.payment.innerLabel)) ^ (gamma / 2)) *
            ((2 : ENNReal) ^ bucketKey * base) ^ (gamma - 1)) *
          ((blockAt S.activeCoarseFamily P W.payment.occurrence).fiber.card :
              ENNReal) ^ (1 - gamma / 2)) <=
      ((winnerSideRetainedSource D S P hdelta R Y fineBucket
          W.outerLabel).shadingDensity * geometryLoss) *
        proposition66AInnerFactor delta
          (bucketShortA W.payment.innerLabel)
          (bucketShortB W.payment.innerLabel)
          (blockAt S.activeCoarseFamily P W.payment.occurrence).fiber.card
          epsilon gamma

/-- The exact unresolved terminal scalar inequality.  No external analytic
factor is absorbed: the outer, geometry, and coefficient losses are visibly
multiplied by the automatic `delta ^ (-lossEta)` payment. -/
def WinnerSideEndpointPackedChosenSectionEightPowerBudget
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (outerLabel : Fin 3 -> Int)
    (sourceCF refinementLoss outerLoss geometryLoss coefficientLoss : ENNReal)
    (epsilon lossEta : Real) : Prop :=
  ((outerLoss * geometryLoss * coefficientLoss ^ (1 - gamma / 2) *
        (delta : ENNReal) ^ (-lossEta)) *
      (proposition66ASectionEightCoefficient delta
          (bucketShortA outerLabel) (bucketShortB outerLabel)
          (endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
            (sourceCF * refinementLoss)) epsilon gamma *
        (delta : ENNReal) ^ (-10 * L.eta W.stage))) <=
    (delta : ENNReal) ^ (-3 * L.eta W.stage)

/-- Fixed-selected-witness bridge from the packed consumer to the endpoint
payment.  All selection and frozen losses are proved automatic; the two
named budget premises expose exactly the remaining outer/geometric analysis
and final Section-Eight scalar power comparison. -/
theorem endpointIdentityLossAwareEq32Payment_of_winnerSide_jointBucket_at
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (Wlong : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (S : StickyScaleCover (fullRefinementDatum D).family delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (Wchosen : WinnerSideEq32ChosenWitness (fullRefinementDatum D) S
      hD.delta_pos P R Y fineBucket rFrozen r hr)
    (base : ENNReal) (bucketKey : Nat)
    (hbandAt : InENNRealDyadicBand base bucketKey
      (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P Wchosen.payment.occurrence)))
    (hbaseOne : 1 <= base) (hbaseTop : base ≠ ∞)
    (outerCFUsed coefficientLoss sourceCF : ENNReal)
    (outerLoss refinementLoss geometryLoss : ENNReal)
    (epsilon : Real) (hgamma0 : 0 <= gamma) (hgammaOne : gamma <= 1)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hjointAverage :
      D.shading.averageMultiplicity <=
        ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
          (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) :
            ENNReal) *
          (winnerSideBucketSource (fullRefinementDatum D) S Y
            fineBucket).averageMultiplicity)
    (hsmall : delta <=
      winnerSideJointBucketEndpointPackedAutomaticSourceLossThreshold
        lossEta gamma)
    (hanalytic : WinnerSideEndpointPackedChosenOuterCoefficientGeometryBudget
      (fullRefinementDatum D) S hD.delta_pos P R Y fineBucket rFrozen r hr
        Wchosen base bucketKey outerCFUsed coefficientLoss sourceCF outerLoss
          refinementLoss geometryLoss epsilon gamma)
    (hsectionEight : WinnerSideEndpointPackedChosenSectionEightPowerBudget
      D hD L Wlong Wchosen.outerLabel sourceCF refinementLoss outerLoss
        geometryLoss coefficientLoss epsilon lossEta) :
    EndpointIdentityLossAwareEq32PaymentAt D hD L Wlong := by
  classical
  let E := fullRefinementDatum D
  let outerLabel := Wchosen.outerLabel
  let payment := Wchosen.payment
  let Rside := winnerSideRetainedOccurrences E S P hD.delta_pos R outerLabel
  let source := winnerSideRetainedSource E S P hD.delta_pos R Y fineBucket
    outerLabel
  let jointLoss : ENNReal :=
    ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
      (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal)
  let winnerLoss : ENNReal := (winnerSideBucketLoss delta : ENNReal)
  let frozenLoss : ENNReal :=
    (frozenComparableLoss (ActiveParentIndex S)
      (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal)
  have hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  have hParent : (activeParentActualTubeDatum S E.shading).IsAdmissible :=
    activeParentActualTubeDatum_isAdmissible_of_sameScale E hE S E.shading
  have hactiveParent : 0 < Fintype.card (ActiveParentIndex S) := by
    have hblocksPos : 0 < (blocks S.activeCoarseFamily P).length :=
      lt_of_le_of_lt (Nat.zero_le payment.occurrence.val)
        payment.occurrence.isLt
    have hblocksCard : (blocks S.activeCoarseFamily P).length <=
        Fintype.card (ActiveParentIndex S) := by
      rw [blocks_length]
      simpa only [Finset.card_univ] using P.length_le_card
    exact hblocksPos.trans_le hblocksCard
  have hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  have hangleNat := selectedParent_angleBucketLoss_le_logarithmic
    (fun i => hE.contained_in_unit_ball i) S hD.delta_pos hdeltaOne P
      payment.occurrence r hr payment.innerLabel
        payment.innerLabel_occupied
  have hangle :
      (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA payment.innerLabel)
          (bucketShortB payment.innerLabel) : ENNReal) <=
        2 * (threeSideDyadicRatioLoss
          (11943936 / (delta : Real)) : ENNReal) := by
    exact_mod_cast hangleNat
  have hautomatic :=
    jointWinnerSide_endpointPackedAutomaticSourceLoss_le_rpow
      E hE S P hactiveParent payment.innerLabel gamma hlossEta hangle hsmall
  have hsourceSupport :
      (IndexedShadingRefinement.restrictTo source
        (selectedOccurrenceFactorization P Rside).index.fine).shading.averageMultiplicity =
          source.averageMultiplicity := by
    dsimp only [source, winnerSideRetainedSource]
    exact selectedOccurrenceFineBucket_restrictTo_fine_averageMultiplicity_eq
      (F := S.activeCoarseFamily)
      P Rside (winnerSideBucketSource E S Y fineBucket)
        (selectedOccurrenceFineIndices P Rside) Finset.Subset.rfl
  have hsourceFrozen : source.averageMultiplicity <=
      frozenLoss *
        (actualRefinementShading payment.assembly).averageMultiplicity := by
    have h := restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement
      payment.assembly
    rw [hsourceSupport] at h
    simpa only [frozenLoss, payment.assembly_loss] using h
  have hwinnerAverage :
      (winnerSideBucketSource E S Y fineBucket).averageMultiplicity <=
        winnerLoss * source.averageMultiplicity := by
    simpa only [E, Rside, source, winnerLoss] using
      Wchosen.selection.2.2.2.2.2.1
  have hsourceToChosen : D.shading.averageMultiplicity <=
      (jointLoss * winnerLoss * frozenLoss) *
        (actualRefinementShading payment.assembly).averageMultiplicity := by
    calc
      D.shading.averageMultiplicity <= jointLoss *
          (winnerSideBucketSource E S Y fineBucket).averageMultiplicity := by
        simpa only [jointLoss, E] using hjointAverage
      _ <= jointLoss * (winnerLoss * source.averageMultiplicity) :=
        mul_le_mul' le_rfl hwinnerAverage
      _ <= jointLoss * (winnerLoss *
          (frozenLoss *
            (actualRefinementShading payment.assembly).averageMultiplicity)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hsourceFrozen)
      _ = (jointLoss * winnerLoss * frozenLoss) *
          (actualRefinementShading payment.assembly).averageMultiplicity := by
        ac_rfl
  rcases hanalytic with ⟨houterCF, houterEq45, hjointScale⟩
  have hchosenEq32 := winnerSide_jointBucket_endpointPackedEq32_at
    E hE S hParent hD.delta_pos hD.delta_le_half P R Y fineBucket
      rFrozen r hr outerLabel Wchosen.selection payment base bucketKey hbandAt
      hbaseOne hbaseTop outerCFUsed coefficientLoss sourceCF outerLoss
      refinementLoss geometryLoss
      (winnerSideEndpointPackedLossWithCoefficient S P payment.innerLabel
        outerLoss geometryLoss coefficientLoss gamma)
      epsilon gamma hgamma0 hgammaOne houterCF houterEq45 hjointScale le_rfl
  let CF : ENNReal := endpointIdentitySourceTauPackingKatzTaoConstant
    delta delta * (sourceCF * refinementLoss)
  let endpointLoss : ENNReal :=
    outerLoss * geometryLoss * coefficientLoss ^ (1 - gamma / 2) *
      (delta : ENNReal) ^ (-lossEta)
  let propFactor : ENNReal := proposition66AFrostmanFactor delta
    (bucketShortA outerLabel) (bucketShortB outerLabel)
    (Fintype.card index) CF epsilon gamma
  have hcoefficient :
      (jointLoss * winnerLoss * frozenLoss) *
          winnerSideEndpointPackedLossWithCoefficient S P payment.innerLabel
            outerLoss geometryLoss coefficientLoss gamma =
        (outerLoss * geometryLoss * coefficientLoss ^ (1 - gamma / 2)) *
          winnerSideJointBucketEndpointPackedAutomaticSourceLoss
            S P payment.innerLabel gamma := by
    dsimp only [jointLoss, winnerLoss, frozenLoss]
    unfold winnerSideJointBucketEndpointPackedAutomaticSourceLoss
      winnerSideJointBucketEndpointPackedAutomaticLoss
      winnerSideEndpointPackedLossWithCoefficient winnerSideEndpointRawLoss
      selectedOccurrenceFrozenSameQPositiveCarrierLoss
    ac_rfl
  have hEq32 : D.shading.averageMultiplicity <= endpointLoss * propFactor := by
    calc
      D.shading.averageMultiplicity <=
          (jointLoss * winnerLoss * frozenLoss) *
            (actualRefinementShading payment.assembly).averageMultiplicity :=
        hsourceToChosen
      _ <= (jointLoss * winnerLoss * frozenLoss) *
          (winnerSideEndpointPackedLossWithCoefficient S P payment.innerLabel
              outerLoss geometryLoss coefficientLoss gamma * propFactor) := by
        apply mul_le_mul' le_rfl
        simpa only [E, CF, propFactor] using hchosenEq32
      _ = ((outerLoss * geometryLoss * coefficientLoss ^ (1 - gamma / 2)) *
          winnerSideJointBucketEndpointPackedAutomaticSourceLoss
            S P payment.innerLabel gamma) * propFactor := by
        rw [← mul_assoc, hcoefficient]
      _ <= ((outerLoss * geometryLoss * coefficientLoss ^ (1 - gamma / 2)) *
          (delta : ENNReal) ^ (-lossEta)) * propFactor :=
        mul_le_mul' (mul_le_mul' le_rfl hautomatic) le_rfl
      _ = endpointLoss * propFactor := by rfl
  refine ⟨bucketShortA outerLabel, bucketShortB outerLabel,
    Fintype.card index, CF, endpointLoss, 1, epsilon, ?_, ?_, ?_⟩
  · simpa only [CF, endpointLoss, propFactor] using hEq32
  · simp
  · simpa only [WinnerSideEndpointPackedChosenSectionEightPowerBudget,
      CF, endpointLoss, ENNReal.one_rpow, mul_one] using hsectionEight

#print axioms
  WinnerSideEndpointPackedChosenOuterCoefficientGeometryBudget
#print axioms WinnerSideEndpointPackedChosenSectionEightPowerBudget
#print axioms
  endpointIdentityLossAwareEq32Payment_of_winnerSide_jointBucket_at

end
end Family8WinnerSideJointBucketEndpointPackedEq32LossAwarePaymentV1
