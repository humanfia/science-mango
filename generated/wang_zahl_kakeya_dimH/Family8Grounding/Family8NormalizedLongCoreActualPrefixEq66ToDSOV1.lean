import Family8Grounding.Family8NormalizedLongCoreCorrelatedEq66ToDSOV1
import Mathlib.Tactic

/-!
# Actual-prefix Equation (66) inputs to the literal long-core DSO

The older correlated-input record stores the stronger budget

`outerPrefix * displayedCoefficient ≤ target`.

Its terminal consumer first weakens this to the only inequality used by the
Equation-(66) connector, namely

`collapsedPrefix ≤ target`.

This file records that literal terminal interface.  In particular it has no
displayed coefficient, selector loss, H-row, or selected-third field.  The
adapter from the older record documents that this is a genuine weakening;
new producers may supply the actual prefix estimate directly.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreActualPrefixEq66ToDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8Eq66CollapsedPrefixLongCoreDSOConnectorV2
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCorrelatedEq66InputsV1
open Family8NormalizedLongCoreCorrelatedEq66InputsV1.NormalizedLongCoreCorrelatedEq66Inputs
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- The exact scalar package read by the terminal collapsed-prefix DSO
connector.  This is intentionally smaller than
`NormalizedLongCoreCorrelatedEq66Inputs`: its prefix field is already the
actual prefix estimate consumed downstream. -/
structure NormalizedLongCoreActualPrefixEq66Inputs
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S) where
  middleScale : NNReal
  middleCount : Nat
  thirdCount : Nat
  collapsedPrefix : ENNReal
  firstLoss : ENNReal
  thirdLoss : ENNReal
  countLoss : ENNReal
  actualPrefixBudget :
    collapsedPrefix ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma
  hCount :
    ((middleCount * thirdCount : Nat) : ENNReal) ≤
      countLoss * (Fintype.card index : ENNReal)
  hAggregateLoss :
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
      (delta : ENNReal) ^ (-3 * P.eta W.stage)

namespace NormalizedLongCoreActualPrefixEq66Inputs

/-- Forget the stronger displayed-coefficient producer interface after it
has produced the actual prefix estimate. -/
def ofCorrelated
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family}
    {S : FiniteScaleSequence delta depth}
    {P : ParameterLadder epsilon0 beta gamma}
    {W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S}
    {iota kappa : Type}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    {fine : UniformTubeFamily (S.tau W.m) iota}
    {G : ConvexFamily kappa}
    {U : StickyScaleCover fine (canonicalBufferedRadius W)}
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal}
    {outputEta : Real}
    (Z : NormalizedLongCoreCorrelatedEq66Inputs D hD C S P W
      fine G U Y Q A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta) :
    NormalizedLongCoreActualPrefixEq66Inputs D hD C S P W where
  middleScale := Z.middleScale
  middleCount := Z.middleCount
  thirdCount := Z.thirdCount
  collapsedPrefix := Z.collapsedPrefix
  firstLoss := Z.firstLoss
  thirdLoss := Z.thirdLoss
  countLoss := Z.countLoss
  actualPrefixBudget := Z.hPrefix
  hCount := Z.hCount
  hAggregateLoss := Z.hAggregateLoss

/-- Consume the genuinely minimal scalar package.  Unlike the older
consumer, this theorem never mentions or reconstructs a displayed
coefficient budget. -/
theorem toDividingScaleOutput
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (Z : NormalizedLongCoreActualPrefixEq66Inputs D hD C S P W)
    (hTauMiddle : S.tau W.m ≤ Z.middleScale)
    (hGammaOne : gamma ≤ 1)
    (hTriple : D.shading.averageMultiplicity ≤
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss))
    (hSmall : delta ≤
      sectionEightThreeScaleActualThreshold gamma
        (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput D P targetEpsilon := by
  let T : LongCoreThreeScaleDSOData D hD C S P W targetEpsilon :=
    LongCoreThreeScaleDSOData.of_eq66_collapsedPrefix
      D hD C S P W hTauMiddle hGammaOne hTriple Z.actualPrefixBudget
        Z.hCount Z.hAggregateLoss hSmall
  exact T.toDividingScaleOutput hTargetEpsilon hGammaOne

#print axioms NormalizedLongCoreActualPrefixEq66Inputs
#print axioms ofCorrelated
#print axioms toDividingScaleOutput

end NormalizedLongCoreActualPrefixEq66Inputs
end
end Family8NormalizedLongCoreActualPrefixEq66ToDSOV1
