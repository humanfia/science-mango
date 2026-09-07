import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSODataV2
import Mathlib.Tactic

/-!
# Equation (66) collapsed-prefix connector for the long-core DSO, V2

Equation (66) naturally leaves its source-to-buffered contribution as one
collapsed prefix.  This file contains only the scalar reassociation needed
after that prefix has actually been bounded by a source-to-buffered
Section-8 factor.  The prefix estimate, the count comparison, the aggregate
loss estimate, and the final smallness premise all remain explicit inputs.

No witness conversion or analytic prefix estimate is asserted here.  V1
used a proposition-only declaration command for a record-valued definition
and is intentionally not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8Eq66CollapsedPrefixLongCoreDSOConnectorV2

open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- Repackage an Equation (66) triple once its entire collapsed prefix has
been bounded by `firstLoss * F(delta, middleScale, middleCount)`.  The
source-to-middle factor is split at the long-core lower scale by exact
multiplicativity, with unit first count. -/
def LongCoreThreeScaleDSOData.of_eq66_collapsedPrefix
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    {middleScale : NNReal}
    (hTauMiddle : S.tau W.m ≤ middleScale)
    {middleCount thirdCount : Nat}
    {collapsedPrefix firstLoss thirdLoss countLoss : ENNReal}
    (hGammaOne : gamma ≤ 1)
    (hTriple : D.shading.averageMultiplicity ≤
      collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              middleScale 1 thirdCount gamma) * thirdLoss))
    (hPrefix : collapsedPrefix ≤ firstLoss *
      sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma)
    (hCount :
      ((middleCount * thirdCount : Nat) : ENNReal) ≤
        countLoss * (Fintype.card index : ENNReal))
    (hAggregateLoss :
      (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
        (delta : ENNReal) ^ (-3 * P.eta W.stage))
    (hSmall : delta ≤
      sectionEightThreeScaleActualThreshold gamma
        (targetEpsilon / 4)) :
    LongCoreThreeScaleDSOData D hD C S P W targetEpsilon := by
  have hTau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hMiddleScale : 0 < middleScale := hTau.trans_le hTauMiddle
  have hGammaTwo : gamma ≤ 2 := hGammaOne.trans (by norm_num)
  have hFactor :
      sectionEightScaleCountFrostmanFactor
          delta (S.tau W.m) 1 gamma *
        sectionEightScaleCountFrostmanFactor
          (S.tau W.m) middleScale middleCount gamma =
      sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma := by
    simpa only [one_mul] using
      (sectionEightScaleCountFrostmanFactor_mul
        hD.delta_pos hTau hMiddleScale hGammaTwo
        (firstCount := 1) (secondCount := middleCount))
  have hReassociated : D.shading.averageMultiplicity ≤
      (firstLoss * sectionEightScaleCountFrostmanFactor
        delta (S.tau W.m) 1 gamma) *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              (S.tau W.m) middleScale middleCount gamma) *
          (thirdLoss * sectionEightScaleCountFrostmanFactor
            middleScale 1 thirdCount gamma)) := by
    calc
      D.shading.averageMultiplicity ≤
          collapsedPrefix *
            (((delta : ENNReal) ^ (10 * P.eta W.stage) *
                sectionEightScaleCountFrostmanFactor
                  middleScale 1 thirdCount gamma) * thirdLoss) := hTriple
      _ ≤ (firstLoss * sectionEightScaleCountFrostmanFactor
            delta middleScale middleCount gamma) *
          (((delta : ENNReal) ^ (10 * P.eta W.stage) *
              sectionEightScaleCountFrostmanFactor
                middleScale 1 thirdCount gamma) * thirdLoss) :=
        mul_le_mul' hPrefix le_rfl
      _ = (firstLoss * sectionEightScaleCountFrostmanFactor
            delta (S.tau W.m) 1 gamma) *
          (((delta : ENNReal) ^ (10 * P.eta W.stage) *
              sectionEightScaleCountFrostmanFactor
                (S.tau W.m) middleScale middleCount gamma) *
            (thirdLoss * sectionEightScaleCountFrostmanFactor
              middleScale 1 thirdCount gamma)) := by
        rw [← hFactor]
        ac_rfl
  exact
    { middleScale := middleScale
      hTauMiddle := hTauMiddle
      firstCount := 1
      middleCount := middleCount
      thirdCount := thirdCount
      countLoss := countLoss
      hCount := by simpa only [one_mul] using hCount
      hSmall := hSmall
      firstAverage := firstLoss *
        sectionEightScaleCountFrostmanFactor
          delta (S.tau W.m) 1 gamma
      middleAverage :=
        (delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            (S.tau W.m) middleScale middleCount gamma
      thirdAverage := thirdLoss *
        sectionEightScaleCountFrostmanFactor
          middleScale 1 thirdCount gamma
      firstLoss := firstLoss
      thirdLoss := thirdLoss
      hTriple := hReassociated
      hFirst := le_rfl
      hMiddle := le_rfl
      hThird := le_rfl
      hAggregateLoss := hAggregateLoss }

#print axioms LongCoreThreeScaleDSOData.of_eq66_collapsedPrefix

end
end Family8Eq66CollapsedPrefixLongCoreDSOConnectorV2
