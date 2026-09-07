import Family8Grounding.Family8CanonicalEndpointBaseThresholdV1
import Family8Grounding.Family8CoreNativeFrozenThirdBundleV1
import Family8Grounding.Family8EndpointLongCoreLiteralDSORecordShellV1
import Family8Grounding.Family8EndpointLongCoreSameAssemblyIdentityTripleV4
import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSODataV2
import Mathlib.Tactic

/-!
# Same-assembly middle/third connector for endpoint LongCore DSO data, V4

V1 is frozen after exact build exposed missing owner namespaces and an
over-aggressive `gcongr` step. V2--V3 exposed legacy monotonicity names not
available in this Lean toolchain. This clean successor uses the checked
`mul_le_mul_left` theorem.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

namespace Family8EndpointSameAssemblyMiddleThirdDSOConnectorV4

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8CanonicalEndpointBaseThresholdV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8EndpointLongCoreLiteralDSORecordShellV1
open Family8EndpointLongCoreSameAssemblyIdentityTripleV4
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index iota kappa : Type}
  [Fintype index] [DecidableEq index]
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {epsilon0 beta gamma targetEpsilon lossEta : Real}
  {F : ConvexFamily iota} {G : ConvexFamily kappa}
  {Q : ConvexFactorization F G} {Y : Shading F}

/-- A no-KT middle witness and a Core-native third bundle on the same literal
assembly fill all non-scalar fields of the endpoint LongCore DSO record. -/
theorem nonempty_longCoreThreeScaleDSOData_of_sameAssembly_middle_third
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hdeltaBase : delta <=
      canonicalEndpointBaseThreshold P targetEpsilon lossEta)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (middleScale : NNReal)
    (hTauMiddle :
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))).tau W.m <= middleScale)
    (middleCount : Nat) (middleFactor countLoss : ENNReal)
    {thirdLoss : ENNReal}
    (X : CoreNativeFrozenThirdBundle Q Y A middleScale thirdLoss gamma)
    (hCount :
      (((1 * (middleCount * X.thirdCount) : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal)))
    {tauAverage : ENNReal}
    (hTau : tauAverage = D.shading.averageMultiplicity)
    (hBounded :
      (IndexedShadingRefinement.restrictTo Y
        Q.index.fine).shading.averageMultiplicity = tauAverage)
    (hMiddleRaw :
      (actualRefinementShading A).averageMultiplicity <=
        A.frozenCoarse.averageMultiplicity * middleFactor)
    (hMiddleAbsorb :
      (4 * (A.loss : ENNReal)) * middleFactor <=
        (delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            ((endpointScaleSequence delta
              (hD.delta_le_half.trans (by norm_num))).tau W.m)
            middleScale middleCount gamma)
    (hAggregateLoss :
      ((1 : ENNReal) * X.thirdLoss) *
          countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    Nonempty (LongCoreThreeScaleDSOData D hD
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))
      P W targetEpsilon) := by
  have hOneFour : (1 : ENNReal) <= 4 := by norm_num
  have hMiddleFour :
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity * middleFactor) := by
    calc
      (actualRefinementShading A).averageMultiplicity <=
          A.frozenCoarse.averageMultiplicity * middleFactor := hMiddleRaw
      _ = 1 * (A.frozenCoarse.averageMultiplicity * middleFactor) := by simp
      _ <= 4 * (A.frozenCoarse.averageMultiplicity * middleFactor) :=
        mul_le_mul_left hOneFour _
  have hTripleRaw :=
    actualDatum_averageMultiplicity_le_identityFirst_middle_third
      D A hTau hBounded hMiddleFour
  have hTriple : D.shading.averageMultiplicity <=
      1 * (((4 * (A.loss : ENNReal)) * middleFactor) * X.thirdAverage) := by
    simpa only [thirdAverage] using hTripleRaw
  exact nonempty_longCoreThreeScaleDSOData_of_endpointIdentity_fields
    D hD P W hdeltaBase middleScale hTauMiddle middleCount X.thirdCount
      countLoss ((4 * (A.loss : ENNReal)) * middleFactor) X.thirdAverage
      X.thirdLoss hCount hTriple hMiddleAbsorb X.hThird hAggregateLoss

#print axioms
  nonempty_longCoreThreeScaleDSOData_of_sameAssembly_middle_third

end
end Family8EndpointSameAssemblyMiddleThirdDSOConnectorV4
