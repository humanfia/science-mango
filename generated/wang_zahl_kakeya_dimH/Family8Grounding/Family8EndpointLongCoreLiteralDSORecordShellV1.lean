import Family8Grounding.Family8CanonicalEndpointBaseThresholdV1
import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSODataV2

/-!
# Endpoint LongCore literal DSO record shell

The one-step endpoint sequence makes the first count, average, loss, and
Section-8 factor literal identities.  This shell freezes those identities in
the final LongCore record and leaves only the same-witness middle/third/count
estimates as explicit mathematical inputs.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreLiteralDSORecordShellV1

open Family8CanonicalEndpointBaseThresholdV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon lossEta : Real}

/-- Assemble the exact endpoint LongCore DSO record once the non-identity
same-witness numerical fields have been proved. -/
theorem nonempty_longCoreThreeScaleDSOData_of_endpointIdentity_fields
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hdeltaBase : delta ≤
      canonicalEndpointBaseThreshold P targetEpsilon lossEta)
    (middleScale : NNReal)
    (hTauMiddle :
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))).tau W.m ≤ middleScale)
    (middleCount thirdCount : Nat)
    (countLoss middleAverage thirdAverage thirdLoss : ENNReal)
    (hCount :
      (((1 * (middleCount * thirdCount) : Nat) : ENNReal) ≤
        countLoss * (Fintype.card index : ENNReal)))
    (hTriple : D.shading.averageMultiplicity ≤
      1 * (middleAverage * thirdAverage))
    (hMiddle : middleAverage ≤
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          ((endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))).tau W.m)
          middleScale middleCount gamma)
    (hThird : thirdAverage ≤ thirdLoss *
      sectionEightScaleCountFrostmanFactor
        middleScale 1 thirdCount gamma)
    (hAggregateLoss :
      ((1 : ENNReal) * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    Nonempty (LongCoreThreeScaleDSOData D hD
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))
      P W targetEpsilon) := by
  let X := endpointLongCoreIdentityFirstFields
    hD.delta_pos (hD.delta_le_half.trans (by norm_num))
    (identityRadiusCoherentCover (fullRefinementDatum D).family) W gamma
  refine Nonempty.intro
    { middleScale := middleScale
      hTauMiddle := hTauMiddle
      firstCount := 1
      middleCount := middleCount
      thirdCount := thirdCount
      countLoss := countLoss
      hCount := hCount
      hSmall := hdeltaBase.trans
        (canonicalEndpointBaseThreshold_le_threeScale
          P targetEpsilon lossEta)
      firstAverage := 1
      middleAverage := middleAverage
      thirdAverage := thirdAverage
      firstLoss := 1
      thirdLoss := thirdLoss
      hTriple := hTriple
      hFirst := ?_
      hMiddle := hMiddle
      hThird := hThird
      hAggregateLoss := hAggregateLoss }
  simpa only [X, endpointLongCoreIdentityFirstFields] using X.hFirst

#print axioms
  nonempty_longCoreThreeScaleDSOData_of_endpointIdentity_fields

end
end Family8EndpointLongCoreLiteralDSORecordShellV1
