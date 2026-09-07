import Family8Grounding.Family8Eq66CollapsedPrefixLongCoreDSOConnectorV2
import Family8Grounding.Family8NormalizedLongCoreCorrelatedEq66InputsV1

/-!
# Correlated Equation (66) inputs to the literal long-core DSO

This is the terminal glue at the V535 correlated-input seam.  The input
record already supplies the correlated prefix estimate, count comparison,
and aggregate loss on one literal normalized LongCore witness.  Once the
actual Equation (66) triple and its scale legality are supplied, the existing
collapsed-prefix connector constructs the literal three-scale record, whose
existing consumer gives `DividingScaleOutput`.

No analytic estimate, selector, or callback is introduced here.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreCorrelatedEq66ToDSOV1

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

/-- Consume one same-object correlated Equation (66) package.  The only
remaining inputs are exactly the arguments that are intentionally not fields
of that package: scale legality, the literal Equation (66) triple, final
smallness, and the two scalar endpoint inequalities required by the existing
DSO consumer. -/
theorem NormalizedLongCoreCorrelatedEq66Inputs.toDividingScaleOutput
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    {iota kappa : Type}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (fine : UniformTubeFamily (S.tau W.m) iota)
    (G : ConvexFamily kappa)
    (U : StickyScaleCover fine (canonicalBufferedRadius W))
    (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily G)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal)
    (outputEta : Real)
    (Z : NormalizedLongCoreCorrelatedEq66Inputs D hD C S P W
      fine G U Y Q A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta)
    (hTauMiddle : S.tau W.m <= Z.middleScale)
    (hGammaOne : gamma <= 1)
    (hTriple : D.shading.averageMultiplicity <=
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss))
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma
        (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput D P targetEpsilon := by
  let T : LongCoreThreeScaleDSOData D hD C S P W targetEpsilon :=
    LongCoreThreeScaleDSOData.of_eq66_collapsedPrefix
      D hD C S P W hTauMiddle hGammaOne hTriple Z.hPrefix
        Z.hCount Z.hAggregateLoss hSmall
  exact T.toDividingScaleOutput hTargetEpsilon hGammaOne

#print axioms
  NormalizedLongCoreCorrelatedEq66Inputs.toDividingScaleOutput

end
end Family8NormalizedLongCoreCorrelatedEq66ToDSOV1
