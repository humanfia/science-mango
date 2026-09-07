import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8Eq66CollapsedPrefixLongCoreDSOConnectorV2

/-!
# Endpoint identity same-q collapsed DSO consumer

At the endpoint identity LongCore the lower stopping scale is exactly the
source scale `delta`.  This thin specialization of the existing collapsed
Equation (66) connector therefore fixes the first count, average, and loss
to one.  It also collapses the remaining two scale intervals by taking the
middle scale to be one and the third count to be one.

The local count remains literally `plankCount * tubesPerPlank`.  No greedy
block, occurrence, side bucket, or shading is selected here, and the inner
Proposition 6.6(A) estimate is not folded into the count comparison.  The
scale-count factor occurs with literal coefficient one.  In particular no
free `collapsedPrefix` parameter can hide an outer loss: every such loss has
to occur in `thirdLoss`, hence also in the aggregate ledger.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentitySameQCollapsedDSOConsumerV1

open Submission.Kakeya.ConvexGeometry
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8Eq66CollapsedPrefixLongCoreDSOConnectorV2
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- Consume a same-q endpoint estimate after its analytic inner estimate has
been kept separate and composed upstream.  The first interval is the exact
identity interval `delta -> delta`; the whole remaining local product count
is assigned to the single middle interval `delta -> 1`.

`hSameQOuter` is the result of composing the specialized `hTriple` and
`hPrefix` of `LongCoreThreeScaleDSOData.of_eq66_collapsedPrefix` with the
loss-free prefix chosen to be the literal scale-count factor.  The other two
substantive inputs are the honest local product-count comparison and the
final loss ledger. -/
theorem dividingScaleOutput_of_endpointIdentity_sameQ_collapsed
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {plankCount tubesPerPlank : Nat}
    {thirdLoss countLoss : ENNReal}
    (hSameQOuter : D.shading.averageMultiplicity <=
      sectionEightScaleCountFrostmanFactor delta 1
          (plankCount * tubesPerPlank) gamma *
        ((delta : ENNReal) ^ (10 * P.eta W.stage) * thirdLoss))
    (hLocalCount :
      ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal))
    (hLossLedger :
      thirdLoss * countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage))
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma
        (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma <= 1) :
    DividingScaleOutput D P targetEpsilon := by
  let C := identityRadiusCoherentCover (fullRefinementDatum D).family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  have hTauOne : S.tau W.m <= (1 : NNReal) := by
    rw [endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W]
    exact hD.delta_le_half.trans (by norm_num)
  have hOneFactor :
      sectionEightScaleCountFrostmanFactor
        (1 : NNReal) 1 1 gamma = 1 :=
    sectionEightScaleCountFrostmanFactor_self_one
      (by norm_num : 0 < (1 : NNReal)) gamma
  have hTriple : D.shading.averageMultiplicity <=
      sectionEightScaleCountFrostmanFactor delta 1
          (plankCount * tubesPerPlank) gamma *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            (1 : NNReal) 1 1 gamma) * thirdLoss) := by
    rw [hOneFactor, mul_one]
    exact hSameQOuter
  let X : LongCoreThreeScaleDSOData D hD C S P W targetEpsilon :=
    LongCoreThreeScaleDSOData.of_eq66_collapsedPrefix
      D hD C S P W hTauOne
      (middleCount := plankCount * tubesPerPlank)
      (thirdCount := 1)
      (collapsedPrefix := sectionEightScaleCountFrostmanFactor delta 1
        (plankCount * tubesPerPlank) gamma)
      (firstLoss := 1)
      (thirdLoss := thirdLoss)
      (countLoss := countLoss)
      hGammaOne hTriple
      (by
        simpa only [one_mul] using
          (le_rfl :
            sectionEightScaleCountFrostmanFactor delta 1
                (plankCount * tubesPerPlank) gamma <=
              sectionEightScaleCountFrostmanFactor delta 1
                (plankCount * tubesPerPlank) gamma))
      (by simpa only [mul_one] using hLocalCount)
      (by simpa only [one_mul] using hLossLedger)
      hSmall
  exact X.toDividingScaleOutput hTargetEpsilon hGammaOne

#print axioms dividingScaleOutput_of_endpointIdentity_sameQ_collapsed

end
end Family8EndpointIdentitySameQCollapsedDSOConsumerV1
