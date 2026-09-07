import Family8Grounding.Family8EndpointIdentitySameQProp66CollapsedDSOBridgeV1
import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8NormalizedLongCoreActualPrefixEq66ToDSOV1
import Mathlib.Tactic

/-!
# Direct Proposition 6.6 product through the minimal actual-prefix terminal

The endpoint same-q Proposition 6.6 branch already produces the whole
outer-times-inner product.  It should not be routed through a graph H-row
factor and a finite-run `hOuterFactor` payment.  This file records the
shorter factor assignment explicitly: the literal scale-count factor is the
collapsed prefix, its first loss is one, and the remaining Proposition 6.6
coefficient is the third loss.

Both the small-`b` Equation-(45) branch and the complementary large-`b`
Lemma-6.9 branch may use this terminal once they have produced the same
Proposition 6.6 product estimate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityProp66DirectActualPrefixTerminalV1

open Submission.Kakeya.ConvexGeometry
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentitySameQProp66CollapsedDSOBridgeV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1.NormalizedLongCoreActualPrefixEq66Inputs
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
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

/-- The minimal actual-prefix record for the direct same-q Proposition 6.6
branch.  No graph, H-row, finite run, or displayed coefficient occurs. -/
def endpointIdentity_actualPrefixInputs_of_prop66A
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF countLoss : ENNReal} {epsilon : Real}
    (hLocalCount :
      ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal))
    (hLossLedger :
      (proposition66ASectionEightCoefficient
          delta a b CF epsilon gamma *
        (delta : ENNReal) ^ (-10 * P.eta W.stage)) *
          countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    NormalizedLongCoreActualPrefixEq66Inputs D hD
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) P W where
  middleScale := 1
  middleCount := plankCount * tubesPerPlank
  thirdCount := 1
  collapsedPrefix := sectionEightScaleCountFrostmanFactor delta 1
    (plankCount * tubesPerPlank) gamma
  firstLoss := 1
  thirdLoss := proposition66ASectionEightCoefficient
      delta a b CF epsilon gamma *
    (delta : ENNReal) ^ (-10 * P.eta W.stage)
  countLoss := countLoss
  actualPrefixBudget := by simp
  hCount := by simpa only [Nat.mul_one] using hLocalCount
  hAggregateLoss := by simpa only [one_mul] using hLossLedger

/-- A direct Proposition 6.6 product supplies the exact `hTriple` consumed by
the minimal actual-prefix terminal. -/
theorem endpointIdentity_actualPrefixTriple_of_prop66A_product
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF countLoss : ENNReal} {epsilon : Real}
    (ha : 0 < a) (hb : 0 < b)
    (hGammaZero : 0 <= gamma) (hGammaOne : gamma <= 1)
    (hProduct : D.shading.averageMultiplicity <=
      proposition66AOuterFactor delta a b plankCount CF epsilon gamma *
        proposition66AInnerFactor delta a b tubesPerPlank epsilon gamma)
    (hLocalCount :
      ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal))
    (hLossLedger :
      (proposition66ASectionEightCoefficient
          delta a b CF epsilon gamma *
        (delta : ENNReal) ^ (-10 * P.eta W.stage)) *
          countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    let Z := endpointIdentity_actualPrefixInputs_of_prop66A
      D hD P W hLocalCount hLossLedger
    D.shading.averageMultiplicity <=
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
  simp only [endpointIdentity_actualPrefixInputs_of_prop66A]
  have hOneFactor :
      sectionEightScaleCountFrostmanFactor (1 : NNReal) 1 1 gamma = 1 :=
    sectionEightScaleCountFrostmanFactor_self_one
      (by norm_num : 0 < (1 : NNReal)) gamma
  rw [hOneFactor, mul_one]
  exact sameQOuter_of_prop66A_product
    D hD P W ha hb hGammaZero hGammaOne hProduct

/-- The direct Proposition 6.6 route reaches `DividingScaleOutput` through
the genuinely minimal actual-prefix consumer.  This is the same scalar
content as the older same-q collapsed adapter, but its factor assignment is
now visible and cannot request `hOuterFactor`. -/
theorem dividingScaleOutput_of_endpointIdentity_prop66A_product_via_actualPrefix
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF countLoss : ENNReal} {epsilon : Real}
    (ha : 0 < a) (hb : 0 < b)
    (hGammaZero : 0 <= gamma)
    (hProduct : D.shading.averageMultiplicity <=
      proposition66AOuterFactor delta a b plankCount CF epsilon gamma *
        proposition66AInnerFactor delta a b tubesPerPlank epsilon gamma)
    (hLocalCount :
      ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal))
    (hLossLedger :
      (proposition66ASectionEightCoefficient
          delta a b CF epsilon gamma *
        (delta : ENNReal) ^ (-10 * P.eta W.stage)) *
          countLoss ^ (1 - gamma / 2) <=
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
  let Z : NormalizedLongCoreActualPrefixEq66Inputs D hD C S P W :=
    endpointIdentity_actualPrefixInputs_of_prop66A
      D hD P W hLocalCount hLossLedger
  have hTauOne : S.tau W.m <= (1 : NNReal) := by
    rw [endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W]
    exact hD.delta_le_half.trans (by norm_num)
  have hTriple : D.shading.averageMultiplicity <=
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
    simpa only [C, S, Z] using
      (endpointIdentity_actualPrefixTriple_of_prop66A_product
        D hD P W ha hb hGammaZero hGammaOne hProduct
          hLocalCount hLossLedger)
  exact Z.toDividingScaleOutput D hD C S P W hTauOne hGammaOne
    hTriple hSmall hTargetEpsilon

/-! ## Loss-aware Equation-(32) entry point

This is the form actually shared by the two outer analytic branches.  The
small-`b` Equation-(45) route and the large-`b` Lemma-6.9 route both finish by
bounding the same source average by one explicit loss times the Proposition
6.6 Equation-(32) factor. -/

/-- Minimal actual-prefix data from a loss-aware Equation-(32) estimate.
The estimate itself is used only by the following `hTriple` theorem. -/
def endpointIdentity_actualPrefixInputs_of_lossAware_eq32
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {a b : NNReal} {totalCount : Nat}
    {CF externalLoss countLoss : ENNReal} {epsilon : Real}
    (hLocalCount : (totalCount : ENNReal) <=
      countLoss * (Fintype.card index : ENNReal))
    (hLossLedger :
      (externalLoss *
        (proposition66ASectionEightCoefficient
            delta a b CF epsilon gamma *
          (delta : ENNReal) ^ (-10 * P.eta W.stage))) *
          countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    NormalizedLongCoreActualPrefixEq66Inputs D hD
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) P W where
  middleScale := 1
  middleCount := totalCount
  thirdCount := 1
  collapsedPrefix := sectionEightScaleCountFrostmanFactor
    delta 1 totalCount gamma
  firstLoss := 1
  thirdLoss := externalLoss *
    (proposition66ASectionEightCoefficient delta a b CF epsilon gamma *
      (delta : ENNReal) ^ (-10 * P.eta W.stage))
  countLoss := countLoss
  actualPrefixBudget := by simp
  hCount := by simpa only [Nat.mul_one] using hLocalCount
  hAggregateLoss := by simpa only [one_mul] using hLossLedger

/-- A loss-aware Equation-(32) estimate is exactly the `hTriple` for the
minimal actual-prefix allocation above. -/
theorem endpointIdentity_actualPrefixTriple_of_lossAware_eq32
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {a b : NNReal} {totalCount : Nat}
    {CF externalLoss countLoss : ENNReal} {epsilon : Real}
    (hEq32 : D.shading.averageMultiplicity <=
      externalLoss * proposition66AFrostmanFactor
        delta a b totalCount CF epsilon gamma)
    (hLocalCount : (totalCount : ENNReal) <=
      countLoss * (Fintype.card index : ENNReal))
    (hLossLedger :
      (externalLoss *
        (proposition66ASectionEightCoefficient
            delta a b CF epsilon gamma *
          (delta : ENNReal) ^ (-10 * P.eta W.stage))) *
          countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    let Z := endpointIdentity_actualPrefixInputs_of_lossAware_eq32
      D hD P W hLocalCount hLossLedger
    D.shading.averageMultiplicity <=
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
  simp only [endpointIdentity_actualPrefixInputs_of_lossAware_eq32]
  have hOneFactor :
      sectionEightScaleCountFrostmanFactor (1 : NNReal) 1 1 gamma = 1 :=
    sectionEightScaleCountFrostmanFactor_self_one
      (by norm_num : 0 < (1 : NNReal)) gamma
  rw [hOneFactor, mul_one]
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hcancel :
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
          (delta : ENNReal) ^ (-10 * P.eta W.stage) = 1 := by
    rw [<- ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
    have hExp : 10 * P.eta W.stage + -10 * P.eta W.stage = 0 := by ring
    rw [hExp, ENNReal.rpow_zero]
  calc
    D.shading.averageMultiplicity <=
        externalLoss * proposition66AFrostmanFactor
          delta a b totalCount CF epsilon gamma := hEq32
    _ = externalLoss *
        (proposition66ASectionEightCoefficient
            delta a b CF epsilon gamma *
          sectionEightScaleCountFrostmanFactor
            delta 1 totalCount gamma) := by
      rw [proposition66AFrostmanFactor_eq_coefficient_mul_sectionEight]
    _ = sectionEightScaleCountFrostmanFactor delta 1 totalCount gamma *
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
          externalLoss * proposition66ASectionEightCoefficient
            delta a b CF epsilon gamma by
        calc
          (delta : ENNReal) ^ (10 * P.eta W.stage) *
              (externalLoss *
                (proposition66ASectionEightCoefficient
                    delta a b CF epsilon gamma *
                  (delta : ENNReal) ^ (-10 * P.eta W.stage))) =
              (externalLoss * proposition66ASectionEightCoefficient
                  delta a b CF epsilon gamma) *
                ((delta : ENNReal) ^ (10 * P.eta W.stage) *
                  (delta : ENNReal) ^ (-10 * P.eta W.stage)) := by
            ac_rfl
          _ = externalLoss * proposition66ASectionEightCoefficient
                delta a b CF epsilon gamma := by rw [hcancel, mul_one]]
      ac_rfl

/-- Direct terminal closure from the common loss-aware Equation-(32) output
of either analytic branch. -/
theorem dividingScaleOutput_of_endpointIdentity_lossAware_eq32_via_actualPrefix
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {a b : NNReal} {totalCount : Nat}
    {CF externalLoss countLoss : ENNReal} {epsilon : Real}
    (hEq32 : D.shading.averageMultiplicity <=
      externalLoss * proposition66AFrostmanFactor
        delta a b totalCount CF epsilon gamma)
    (hLocalCount : (totalCount : ENNReal) <=
      countLoss * (Fintype.card index : ENNReal))
    (hLossLedger :
      (externalLoss *
        (proposition66ASectionEightCoefficient
            delta a b CF epsilon gamma *
          (delta : ENNReal) ^ (-10 * P.eta W.stage))) *
          countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage))
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma <= 1) :
    DividingScaleOutput D P targetEpsilon := by
  let C := identityRadiusCoherentCover (fullRefinementDatum D).family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let Z : NormalizedLongCoreActualPrefixEq66Inputs D hD C S P W :=
    endpointIdentity_actualPrefixInputs_of_lossAware_eq32
      D hD P W hLocalCount hLossLedger
  have hTauOne : S.tau W.m <= (1 : NNReal) := by
    rw [endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W]
    exact hD.delta_le_half.trans (by norm_num)
  have hTriple : D.shading.averageMultiplicity <=
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
    simpa only [C, S, Z] using
      (endpointIdentity_actualPrefixTriple_of_lossAware_eq32
        D hD P W hEq32 hLocalCount hLossLedger)
  exact Z.toDividingScaleOutput D hD C S P W hTauOne hGammaOne
    hTriple hSmall hTargetEpsilon

#print axioms endpointIdentity_actualPrefixInputs_of_prop66A
#print axioms endpointIdentity_actualPrefixTriple_of_prop66A_product
#print axioms
  dividingScaleOutput_of_endpointIdentity_prop66A_product_via_actualPrefix
#print axioms endpointIdentity_actualPrefixInputs_of_lossAware_eq32
#print axioms endpointIdentity_actualPrefixTriple_of_lossAware_eq32
#print axioms
  dividingScaleOutput_of_endpointIdentity_lossAware_eq32_via_actualPrefix

end
end Family8EndpointIdentityProp66DirectActualPrefixTerminalV1
