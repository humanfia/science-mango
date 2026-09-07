import Family8Grounding.Family8CanonicalEndpointBaseThresholdV1
import Family8Grounding.Family8EndpointSameAssemblyMiddleThirdDSOConnectorV4
import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSODataV2
import Family8Grounding.Family8SelectedFineEndpointCountComparisonV1
import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# Selected-fine same-assembly endpoint DSO connector, V3

V2 is frozen after exposing three owner/simplifier seams. This clean
successor imports the scale-count factor owner, normalizes the natural cast
of one explicitly in the count field, and lets the simplifier discharge the
unit ENNReal rpow in the aggregate field.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

namespace Family8EndpointSelectedFineSameAssemblyDSOConnectorV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalEndpointBaseThresholdV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8EndpointSameAssemblyMiddleThirdDSOConnectorV4
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8SelectedFineEndpointCountComparisonV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {sourceDelta scale rho : NNReal}
  {index iota : Type}
  [Fintype index] [DecidableEq index]
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily scale iota}
  {epsilon0 beta gamma targetEpsilon lossEta : Real}

/-- The selected-fine middle witness and same-assembly third bundle fill the
endpoint DSO record once their two scalar losses fit the reserved powers. -/
theorem nonempty_longCoreThreeScaleDSOData_of_selectedFine_middle_third
    (D : ActualTubeDatum sourceDelta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence sourceDelta
        (hD.delta_le_half.trans (by norm_num))))
    (hdeltaBase : sourceDelta <=
      canonicalEndpointBaseThreshold P targetEpsilon lossEta)
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hscale : scale <= rho) (hcoarse : S.activeCoarse.Nonempty)
    (hM : forall k, k ∈ S.activeCoarse -> (S.fiber k).card <= 1)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (boundedFiberCoarseTubePartition S hscale hcoarse 1 hM
        ).asConvexFactorization Y 1)
    (middleScale : NNReal)
    (hTauMiddle :
      (endpointScaleSequence sourceDelta
        (hD.delta_le_half.trans (by norm_num))).tau W.m <= middleScale)
    (selectedFine : Finset iota) (hselectedFine : selectedFine ⊆ S.activeFine)
    (q : Fin (selectedFineParentValues S selectedFine).card)
    (selected : Finset {i // i ∈
      (selectedFineScaleCover S selectedFine hselectedFine).fiber q})
    (hcoarseCard : S.coarseCard = Fintype.card index)
    (middleFactor : ENNReal) {thirdLoss : ENNReal}
    (X : CoreNativeFrozenThirdBundle
      (boundedFiberCoarseTubePartition S hscale hcoarse 1 hM
        ).asConvexFactorization Y A middleScale thirdLoss gamma)
    {tauAverage : ENNReal}
    (hTau : tauAverage = D.shading.averageMultiplicity)
    (hBounded :
      (IndexedShadingRefinement.restrictTo Y
        (boundedFiberCoarseTubePartition S hscale hcoarse 1 hM
          ).asConvexFactorization.index.fine).shading.averageMultiplicity =
        tauAverage)
    (hMiddleRaw :
      (actualRefinementShading A).averageMultiplicity <=
        A.frozenCoarse.averageMultiplicity * middleFactor)
    (hMiddleAbsorb :
      (4 * (A.loss : ENNReal)) * middleFactor <=
        (sourceDelta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            ((endpointScaleSequence sourceDelta
              (hD.delta_le_half.trans (by norm_num))).tau W.m)
            middleScale selected.card gamma)
    (hThirdPower : X.thirdLoss <=
      (sourceDelta : ENNReal) ^ (-3 * P.eta W.stage)) :
    Nonempty (LongCoreThreeScaleDSOData D hD
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence sourceDelta
        (hD.delta_le_half.trans (by norm_num)))
      P W targetEpsilon) := by
  have hCountRaw := selectedFine_endpoint_countComparison
    S selectedFine hselectedFine q selected 1 hM hcoarseCard
  have hCount :
      (((1 * (selected.card * X.thirdCount) : Nat) : ENNReal) <=
        (1 : ENNReal) * (Fintype.card index : ENNReal)) := by
    simpa only [thirdCount, Nat.cast_one] using hCountRaw
  have hAggregate :
      ((1 : ENNReal) * X.thirdLoss) *
          (1 : ENNReal) ^ (1 - gamma / 2) <=
        (sourceDelta : ENNReal) ^ (-3 * P.eta W.stage) := by
    simpa using hThirdPower
  exact nonempty_longCoreThreeScaleDSOData_of_sameAssembly_middle_third
    D hD P W hdeltaBase A middleScale hTauMiddle selected.card
      middleFactor 1 X hCount hTau hBounded hMiddleRaw hMiddleAbsorb
      hAggregate

#print axioms
  nonempty_longCoreThreeScaleDSOData_of_selectedFine_middle_third

end
end Family8EndpointSelectedFineSameAssemblyDSOConnectorV3
