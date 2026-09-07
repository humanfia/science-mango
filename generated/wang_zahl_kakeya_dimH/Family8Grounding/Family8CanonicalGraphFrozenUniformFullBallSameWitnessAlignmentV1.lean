import Family8Grounding.Family8CanonicalGraphFrozenUniformFullBallTailBudgetAdapterV1
import Mathlib.Tactic

/-!
# Same-witness alignment from one uniform full ball to one frozen graph band

The full-ball construction carries a three-dimensional packing, whereas the
lower-bucket construction carries a planar exact-card band.  Existing
projection identities have the opposite payment direction.  This module
therefore records the smallest missing same-object datum: the literal final
fine shading, ball radius and centre are indices, as are `R`, the graph band,
the fibre floor and the coefficient; the only field is the missing product
payment.  No selected object can be changed through an equality field.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenUniformFullBallSameWitnessAlignmentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenQuantitativeLowerBucketFirstHitPaymentV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CanonicalGraphFrozenUniformFullBallTailBudgetAdapterV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u v w

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- Exact local-ball to graph-band alignment.  All witness-bearing terms are
indices; the sole field is precisely the missing geometry. -/
structure SameGraphUniformFullBallWitnessAlignment
    {localIndex : Type v} [Fintype localIndex]
    {localFamily : ConvexFamily localIndex}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (bandLevel : Nat) (fibreFloor coefficient : ENNReal)
    (finalFine : Shading localFamily) (ballRadius : NNReal)
    (center : Space) : Prop where
  localBall_payment :
    coefficient *
        volume (finalFine.shadedUnion ∩
          Metric.ball center (ballRadius : Real)) <=
      fibreFloor * sameGraphPositiveExactCardBandVolume R bandLevel

/-- Consume the endpoint inequality already evaluated at the fixed centre.
No packing, graph, band, centre or fibre floor is selected here. -/
theorem sameGraphQuantitativeLowerBucketTailBudget_of_fixedUniformFullBallAt
    {endpointIndex : Type u} [Fintype endpointIndex]
    {localIndex : Type v} [Fintype localIndex]
    {localFamily : ConvexFamily localIndex}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (bandLevel : Nat)
    (fibreFloor displayed density : ENNReal)
    (a b ballRadius : NNReal) (beta absorbExponent : Real)
    (finalFine : Shading localFamily) (center : Space)
    (hleft : sameGraphQuantitativeLowerBucketTailLeft R displayed <=
      density * ((a : ENNReal) * (b : ENNReal)) *
        volume (Metric.ball (0 : Space) (ballRadius : Real)))
    (hfullBallAt :
      density * ((a : ENNReal) * (b : ENNReal)) *
          volume (Metric.ball (0 : Space) (ballRadius : Real)) <=
        ((a : ENNReal) ^ (-absorbExponent) *
          (Fintype.card endpointIndex : ENNReal) ^ (1 - beta / 2)) *
            volume (finalFine.shadedUnion ∩
              Metric.ball center (ballRadius : Real)))
    (hAlignment : SameGraphUniformFullBallWitnessAlignment
      R bandLevel fibreFloor
        ((a : ENNReal) ^ (-absorbExponent) *
          (Fintype.card endpointIndex : ENNReal) ^ (1 - beta / 2))
        finalFine ballRadius center) :
    SameGraphQuantitativeLowerBucketTailBudget
      R bandLevel fibreFloor displayed := by
  exact sameGraphQuantitativeLowerBucketTailBudget_of_uniformFullBallScalarSandwich
    (iota := endpointIndex) R bandLevel fibreFloor displayed density
      (volume (finalFine.shadedUnion ∩
        Metric.ball center (ballRadius : Real)))
      a b ballRadius beta absorbExponent hleft hfullBallAt
        hAlignment.localBall_payment

/-- Consume the universal final conjunct of an already fixed endpoint at a
caller-supplied point of its exact final coarse shading. -/
theorem sameGraphQuantitativeLowerBucketTailBudget_of_fixedUniformFullBallPayload
    {endpointIndex : Type u} [Fintype endpointIndex]
    {localFineIndex : Type v} [Fintype localFineIndex]
    {localFineFamily : ConvexFamily localFineIndex}
    {localCoarseIndex : Type w} [Fintype localCoarseIndex]
    {localCoarseFamily : ConvexFamily localCoarseIndex}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (bandLevel : Nat)
    (fibreFloor displayed density : ENNReal)
    (a b ballRadius : NNReal) (beta absorbExponent : Real)
    (finalFine : Shading localFineFamily)
    (finalCoarse : Shading localCoarseFamily) (center : Space)
    (hcenter : center ∈ finalCoarse.shadedUnion)
    (hleft : sameGraphQuantitativeLowerBucketTailLeft R displayed <=
      density * ((a : ENNReal) * (b : ENNReal)) *
        volume (Metric.ball (0 : Space) (ballRadius : Real)))
    (hfullBall : forall x, x ∈ finalCoarse.shadedUnion ->
      density * ((a : ENNReal) * (b : ENNReal)) *
          volume (Metric.ball (0 : Space) (ballRadius : Real)) <=
        ((a : ENNReal) ^ (-absorbExponent) *
          (Fintype.card endpointIndex : ENNReal) ^ (1 - beta / 2)) *
            volume (finalFine.shadedUnion ∩
              Metric.ball x (ballRadius : Real)))
    (hAlignment : SameGraphUniformFullBallWitnessAlignment
      R bandLevel fibreFloor
        ((a : ENNReal) ^ (-absorbExponent) *
          (Fintype.card endpointIndex : ENNReal) ^ (1 - beta / 2))
        finalFine ballRadius center) :
    SameGraphQuantitativeLowerBucketTailBudget
      R bandLevel fibreFloor displayed := by
  exact sameGraphQuantitativeLowerBucketTailBudget_of_fixedUniformFullBallAt
    (endpointIndex := endpointIndex) R bandLevel fibreFloor displayed density
      a b ballRadius beta absorbExponent finalFine center hleft
        (hfullBall center hcenter) hAlignment

#print axioms SameGraphUniformFullBallWitnessAlignment
#print axioms
  sameGraphQuantitativeLowerBucketTailBudget_of_fixedUniformFullBallAt
#print axioms
  sameGraphQuantitativeLowerBucketTailBudget_of_fixedUniformFullBallPayload

end
end Family8CanonicalGraphFrozenUniformFullBallSameWitnessAlignmentV1
