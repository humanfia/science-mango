import Family8Grounding.Family8EndpointIdentitySameQProp66CollapsedDSOBridgeV1

/-!
# Loss-aware same-object Proposition 6.6(A) endpoint bridge

This sibling permits one explicit source-average loss in front of the same
Proposition 6.6(A) outer-times-inner product.  The loss is inserted exactly
once into `thirdLoss`, next to the Section-8 coefficient and inverse gain.
The literal same-object product count and its `countLoss` comparison are
unchanged.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentitySameQProp66CollapsedLossAwareDSOBridgeV1

open Submission.Kakeya.ConvexGeometry
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentitySameQCollapsedDSOConsumerV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66ASectionEightCollapsedAlgebraV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- Reassociate a loss-aware same-object Proposition 6.6(A) estimate without
changing its literal product count.  `externalLoss` occurs exactly once in
the resulting third loss. -/
theorem sameQOuter_of_lossAware_prop66A_product
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF externalLoss : ENNReal} {epsilon : Real}
    (ha : 0 < a) (hb : 0 < b)
    (hGammaZero : 0 <= gamma) (hGammaOne : gamma <= 1)
    (hProduct : D.shading.averageMultiplicity <=
      externalLoss *
        (proposition66AOuterFactor
            delta a b plankCount CF epsilon gamma *
          proposition66AInnerFactor
            delta a b tubesPerPlank epsilon gamma)) :
    D.shading.averageMultiplicity <=
      sectionEightScaleCountFrostmanFactor delta 1
          (plankCount * tubesPerPlank) gamma *
        ((delta : ENNReal) ^ (10 * P.eta W.stage) *
          (externalLoss *
            (proposition66ASectionEightCoefficient
                delta a b CF epsilon gamma *
              (delta : ENNReal) ^ (-10 * P.eta W.stage)))) := by
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hcancel :
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
          (delta : ENNReal) ^ (-10 * P.eta W.stage) = 1 := by
    rw [<- ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
    have hExp :
        10 * P.eta W.stage + -10 * P.eta W.stage = 0 := by
      ring
    rw [hExp, ENNReal.rpow_zero]
  calc
    D.shading.averageMultiplicity <=
        externalLoss *
          (proposition66AOuterFactor
              delta a b plankCount CF epsilon gamma *
            proposition66AInnerFactor
              delta a b tubesPerPlank epsilon gamma) := hProduct
    _ = externalLoss *
          (proposition66ASectionEightCoefficient
              delta a b CF epsilon gamma *
            sectionEightScaleCountFrostmanFactor delta 1
              (plankCount * tubesPerPlank) gamma) := by
      rw [proposition66AOuter_mul_inner_eq_coefficient_mul_sectionEight
        hD.delta_pos ha hb hGammaZero hGammaOne]
    _ = sectionEightScaleCountFrostmanFactor delta 1
          (plankCount * tubesPerPlank) gamma *
        ((delta : ENNReal) ^ (10 * P.eta W.stage) *
          (externalLoss *
            (proposition66ASectionEightCoefficient
                delta a b CF epsilon gamma *
              (delta : ENNReal) ^ (-10 * P.eta W.stage)))) := by
      rw [show
        (delta : ENNReal) ^ (10 * P.eta W.stage) *
            (externalLoss *
              (proposition66ASectionEightCoefficient
                  delta a b CF epsilon gamma *
                (delta : ENNReal) ^ (-10 * P.eta W.stage))) =
          externalLoss *
            proposition66ASectionEightCoefficient
              delta a b CF epsilon gamma by
        calc
          (delta : ENNReal) ^ (10 * P.eta W.stage) *
              (externalLoss *
                (proposition66ASectionEightCoefficient
                    delta a b CF epsilon gamma *
                  (delta : ENNReal) ^ (-10 * P.eta W.stage))) =
              (externalLoss *
                proposition66ASectionEightCoefficient
                  delta a b CF epsilon gamma) *
                ((delta : ENNReal) ^ (10 * P.eta W.stage) *
                  (delta : ENNReal) ^ (-10 * P.eta W.stage)) := by
            ac_rfl
          _ = externalLoss *
              proposition66ASectionEightCoefficient
                delta a b CF epsilon gamma := by
            rw [hcancel, mul_one]]
      ac_rfl

/-- Endpoint closure with one explicit source-average loss.  The loss is
paid linearly once in the third-loss ledger; it is not folded into
`countLoss` and therefore is not raised to `1 - gamma / 2`. -/
theorem dividingScaleOutput_of_endpointIdentity_sameQ_lossAware_prop66A_product
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF externalLoss countLoss : ENNReal} {epsilon : Real}
    (ha : 0 < a) (hb : 0 < b)
    (hGammaZero : 0 <= gamma)
    (hProduct : D.shading.averageMultiplicity <=
      externalLoss *
        (proposition66AOuterFactor
            delta a b plankCount CF epsilon gamma *
          proposition66AInnerFactor
            delta a b tubesPerPlank epsilon gamma))
    (hLocalCount :
      ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal))
    (hLossLedger :
      (externalLoss *
        (proposition66ASectionEightCoefficient
            delta a b CF epsilon gamma *
          (delta : ENNReal) ^ (-10 * P.eta W.stage))) *
          countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage))
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma
        (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma <= 1) :
    DividingScaleOutput D P targetEpsilon := by
  exact dividingScaleOutput_of_endpointIdentity_sameQ_collapsed
    D hD P W
    (plankCount := plankCount)
    (tubesPerPlank := tubesPerPlank)
    (thirdLoss := externalLoss *
      (proposition66ASectionEightCoefficient
          delta a b CF epsilon gamma *
        (delta : ENNReal) ^ (-10 * P.eta W.stage)))
    (countLoss := countLoss)
    (sameQOuter_of_lossAware_prop66A_product D hD P W ha hb
      hGammaZero hGammaOne hProduct)
    hLocalCount hLossLedger hSmall hTargetEpsilon hGammaOne

#print axioms sameQOuter_of_lossAware_prop66A_product
#print axioms
  dividingScaleOutput_of_endpointIdentity_sameQ_lossAware_prop66A_product

end
end Family8EndpointIdentitySameQProp66CollapsedLossAwareDSOBridgeV1
