import Family8Grounding.Family8Eq66CollapsedPrefixLongCoreDSOConnectorV2
import Family8Grounding.Family8SameObjectCorrelatedSelectedThirdCertificateV1
import Mathlib.Tactic

/-!
# Normalized LongCore correlated inputs for the Eq. 66 V2 connector

This record is a producer interface.  It freezes a normalized LongCore
witness `W`, one cover `U` at its canonical buffered radius, one shading
`Y`, one factorization and assembly `A`, and one card-scale mass `X`.

It does not construct a DSO and it does not discharge any geometric
producer obligation.  Its only derived theorem is the correlated `hPrefix`
inequality consumed by
`Family8Eq66CollapsedPrefixLongCoreDSOConnectorV2`; the count and aggregate
loss inequalities remain literal record fields with exactly the V2 shapes.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreCorrelatedEq66InputsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8SameObjectCorrelatedSelectedThirdCertificateV1
open Family8SameObjectCorrelatedSelectedThirdCertificateV1.SameObjectCorrelatedSelectedThirdCertificate
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Exact producer-facing scalar inputs for V2, indexed by the same
normalized witness and selected-third objects throughout. -/
structure NormalizedLongCoreCorrelatedEq66Inputs
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
    (outputEta : Real) where
  selectedThird :
    SameObjectCorrelatedSelectedThirdCertificate (delta := delta)
      U Y Q A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta
  middleScale : NNReal
  middleCount : Nat
  thirdCount : Nat
  thirdCount_eq : thirdCount = Fintype.card kappa
  collapsedPrefix : ENNReal
  outerPrefix : ENNReal
  firstLoss : ENNReal
  thirdLoss : ENNReal
  countLoss : ENNReal
  collapsedPrefix_le_actualThird :
    collapsedPrefix <= outerPrefix * selectedThird.actualThirdAverage
  correlatedPrefixBudget :
    outerPrefix *
        (selectorLoss *
          (128 * (delta : ENNReal) ^ (-outputEta) * X)) <=
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma
  hCount :
    ((middleCount * thirdCount : Nat) : ENNReal) <=
      countLoss * (Fintype.card index : ENNReal)
  hAggregateLoss :
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) <=
      (delta : ENNReal) ^ (-3 * P.eta W.stage)

namespace NormalizedLongCoreCorrelatedEq66Inputs

/-- The exact `hPrefix` argument of the V2 Eq. 66 connector.  The source
coefficient is compared only after multiplication by `outerPrefix`; no
standalone estimate for `CKT` is produced. -/
theorem hPrefix
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
    Z.collapsedPrefix <=
      Z.firstLoss * sectionEightScaleCountFrostmanFactor
        delta Z.middleScale Z.middleCount gamma := by
  calc
    Z.collapsedPrefix <=
        Z.outerPrefix * Z.selectedThird.actualThirdAverage :=
      Z.collapsedPrefix_le_actualThird
    _ <= Z.firstLoss * sectionEightScaleCountFrostmanFactor
          delta Z.middleScale Z.middleCount gamma :=
      prefix_mul_actualThirdAverage_le_of_correlatedBudget
        Z.selectedThird Z.correlatedPrefixBudget

#print axioms NormalizedLongCoreCorrelatedEq66Inputs
#print axioms hPrefix

end NormalizedLongCoreCorrelatedEq66Inputs
end
end Family8NormalizedLongCoreCorrelatedEq66InputsV1
