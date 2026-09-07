import Family8Grounding.Family8WinnerSideJointBucketLargeBLemma69ConsumerV1
import Family8Grounding.Family8EndpointIdentitySameCoreHighLossAwareEq32IntegrationV1
import Family8Grounding.Family8SelectedOccurrenceFineBucketSupportV1
import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Mathlib.Tactic

/-!
# Loss-aware endpoint payment from one fixed winner-side large-b witness

This is the thin payment boundary for the large-`b` branch.  It keeps the
literal product count stored by the already selected witness, transports the
source average to that witness's actual refinement, and packages the fixed
large-`b` conclusion into the endpoint loss-aware Equation-(32) payment.

The only scalar premise added here is the terminal Section-Eight ledger for
these exact selected objects.  In particular, no callback over other possible
winner-side witnesses and no packed-consumer loss are introduced.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8WinnerSideJointBucketLargeBLossAwarePaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8EndpointIdentitySameCoreHighLossAwareEq32IntegrationV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66ASectionEightCollapsedAlgebraV1
open Family8Prop66InnerScaleMismatchAbsorptionV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFineBucketSupportV1
open Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SourceActiveFineActualAverageIdentityV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8WinnerSideJointBucketLargeBLemma69ConsumerV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Package one already selected large-`b` witness into the endpoint payment.

`hjointAverage` and `hwinnerAverage` are the two boundary inequalities from
the endpoint joint-density and winner-side selections.  The frozen-assembly
part of the source-average transport is reconstructed from `Wfix`.  The local
count is the exact `Rside.card * fiber.card` stored in `Wfix`, with
`countLoss = 2`.
-/
theorem endpointIdentityLossAwareEq32Payment_of_winnerSide_largeB_fixedW
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (Wlong : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (S : StickyScaleCover (fullRefinementDatum D).family rho)
    (hrho : 0 < rho) (hrhoEq : rho = delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (labelOuter : Fin 3 -> Int)
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (Wfix : WinnerSideLargeBLemma69PaymentWitness S hrho P
      (winnerSideRetainedOccurrences
        (fullRefinementDatum D) S P hrho R labelOuter)
      (winnerSideRetainedSource
        (fullRefinementDatum D) S P hrho R Y fineBucket labelOuter)
      rFrozen r hr)
    (jointLoss outerKT outerLoss innerLoss : ENNReal)
    (epsilon : Real)
    (hjointAverage :
      D.shading.averageMultiplicity <=
        jointLoss *
          (winnerSideBucketSource
            (fullRefinementDatum D) S Y fineBucket).averageMultiplicity)
    (hwinnerAverage :
      (winnerSideBucketSource
        (fullRefinementDatum D) S Y fineBucket).averageMultiplicity <=
        (winnerSideBucketLoss rho : ENNReal) *
          (winnerSideRetainedSource
            (fullRefinementDatum D) S P hrho R Y fineBucket
              labelOuter).averageMultiplicity)
    (hLargeB : WinnerSideLargeBLemma69ConclusionAt S P
      (winnerSideRetainedOccurrences
        (fullRefinementDatum D) S P hrho R labelOuter)
      (winnerSideRetainedSource
        (fullRefinementDatum D) S P hrho R Y fineBucket labelOuter)
      rFrozen Wfix.assembly Wfix.occurrence labelOuter Wfix.innerLabel
        outerKT outerLoss innerLoss epsilon gamma)
    (hsectionEight :
      ((jointLoss * (winnerSideBucketLoss rho : ENNReal) *
            (frozenComparableLoss (ActiveParentIndex S)
              (Option (Fin (blocks S.activeCoarseFamily P).length)) :
                ENNReal)) *
          (4 * outerLoss * innerLoss *
            prop66InnerScaleMismatchLoss
              (bucketShortA labelOuter) (bucketShortB labelOuter)
              (bucketShortA Wfix.innerLabel)
              (bucketShortB Wfix.innerLabel) gamma)) *
        (proposition66ASectionEightCoefficient delta
            (bucketShortA labelOuter) (bucketShortB labelOuter)
            outerKT epsilon gamma *
          (delta : ENNReal) ^ (-10 * L.eta Wlong.stage)) *
        (2 : ENNReal) ^ (1 - gamma / 2) <=
          (delta : ENNReal) ^ (-3 * L.eta Wlong.stage)) :
    EndpointIdentityLossAwareEq32PaymentAt D hD L Wlong := by
  classical
  subst rho
  let E := fullRefinementDatum D
  let Rside := winnerSideRetainedOccurrences E S P hrho R labelOuter
  let source := winnerSideRetainedSource
    E S P hrho R Y fineBucket labelOuter
  let winnerLoss : ENNReal := winnerSideBucketLoss delta
  let frozenLoss : ENNReal :=
    frozenComparableLoss (ActiveParentIndex S)
      (Option (Fin (blocks S.activeCoarseFamily P).length))
  let sourceLoss : ENNReal := jointLoss * winnerLoss * frozenLoss
  let largeBLoss : ENNReal :=
    4 * outerLoss * innerLoss *
      prop66InnerScaleMismatchLoss
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        (bucketShortA Wfix.innerLabel) (bucketShortB Wfix.innerLabel) gamma
  let externalLoss : ENNReal := sourceLoss * largeBLoss
  let totalCount : Nat :=
    Rside.card *
      (blockAt S.activeCoarseFamily P Wfix.occurrence).fiber.card
  have hsourceSupport :
      (IndexedShadingRefinement.restrictTo source
        (selectedOccurrenceFactorization P Rside).index.fine).shading.averageMultiplicity =
          source.averageMultiplicity := by
    dsimp only [source, winnerSideRetainedSource]
    exact
      selectedOccurrenceFineBucket_restrictTo_fine_averageMultiplicity_eq
        (F := S.activeCoarseFamily) P Rside
        (winnerSideBucketSource E S Y fineBucket)
        (selectedOccurrenceFineIndices P Rside) Finset.Subset.rfl
  have hsourceFrozen : source.averageMultiplicity <=
      frozenLoss *
        (actualRefinementShading Wfix.assembly).averageMultiplicity := by
    have h :=
      restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement
        Wfix.assembly
    rw [hsourceSupport] at h
    simpa only [frozenLoss, Wfix.assembly_loss] using h
  have hwinnerAverage' :
      (winnerSideBucketSource E S Y fineBucket).averageMultiplicity <=
        winnerLoss * source.averageMultiplicity := by
    simpa only [E, Rside, source, winnerLoss] using hwinnerAverage
  have hsourceToFixed : D.shading.averageMultiplicity <=
      sourceLoss *
        (actualRefinementShading Wfix.assembly).averageMultiplicity := by
    calc
      D.shading.averageMultiplicity <=
          jointLoss *
            (winnerSideBucketSource E S Y fineBucket).averageMultiplicity := by
        simpa only [E] using hjointAverage
      _ <= jointLoss * (winnerLoss * source.averageMultiplicity) :=
        mul_le_mul' le_rfl hwinnerAverage'
      _ <= jointLoss * (winnerLoss *
          (frozenLoss *
            (actualRefinementShading Wfix.assembly).averageMultiplicity)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hsourceFrozen)
      _ = sourceLoss *
          (actualRefinementShading Wfix.assembly).averageMultiplicity := by
        dsimp only [sourceLoss]
        ac_rfl
  have hfixedLargeB :
      (actualRefinementShading Wfix.assembly).averageMultiplicity <=
        largeBLoss * proposition66AFrostmanFactor delta
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          totalCount outerKT epsilon gamma := by
    simpa only [WinnerSideLargeBLemma69ConclusionAt, Rside, source,
      totalCount, largeBLoss] using hLargeB
  have hEq32 : D.shading.averageMultiplicity <=
      externalLoss * proposition66AFrostmanFactor delta
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        totalCount outerKT epsilon gamma := by
    calc
      D.shading.averageMultiplicity <=
          sourceLoss *
            (actualRefinementShading Wfix.assembly).averageMultiplicity :=
        hsourceToFixed
      _ <= sourceLoss *
          (largeBLoss * proposition66AFrostmanFactor delta
            (bucketShortA labelOuter) (bucketShortB labelOuter)
            totalCount outerKT epsilon gamma) :=
        mul_le_mul' le_rfl hfixedLargeB
      _ = externalLoss * proposition66AFrostmanFactor delta
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          totalCount outerKT epsilon gamma := by
        dsimp only [externalLoss]
        ac_rfl
  have hactiveNat : Fintype.card (ActiveParentIndex S) <=
      Fintype.card index := by
    rw [Fintype.card_coe]
    exact
      (activeCoarse_card_le_activeFine_card S).trans
        (Finset.card_le_univ S.activeFine)
  have hactive : (Fintype.card (ActiveParentIndex S) : ENNReal) <=
      (Fintype.card index : ENNReal) := by
    exact_mod_cast hactiveNat
  have hcount : (totalCount : ENNReal) <=
      (2 : ENNReal) * (Fintype.card index : ENNReal) := by
    calc
      (totalCount : ENNReal) <=
          (2 : ENNReal) *
            (Fintype.card (ActiveParentIndex S) : ENNReal) := by
        dsimp only [totalCount, Rside, E]
        exact_mod_cast Wfix.count_active
      _ <= (2 : ENNReal) * (Fintype.card index : ENNReal) :=
        mul_le_mul' le_rfl hactive
  refine
    ⟨bucketShortA labelOuter, bucketShortB labelOuter, totalCount,
      outerKT, externalLoss, 2, epsilon, hEq32, hcount, ?_⟩
  simpa only [externalLoss, sourceLoss, winnerLoss, frozenLoss, largeBLoss]
    using hsectionEight

#print axioms
  endpointIdentityLossAwareEq32Payment_of_winnerSide_largeB_fixedW

end
end Family8WinnerSideJointBucketLargeBLossAwarePaymentV1
