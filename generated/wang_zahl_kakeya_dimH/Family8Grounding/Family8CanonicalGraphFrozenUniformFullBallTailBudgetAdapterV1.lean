import Family8Grounding.Family8CanonicalGraphFrozenQuantitativeLowerBucketFirstHitPaymentV1
import Family8Grounding.Family8PlankRetainedOwnerUniformFullBallPowerEndpointV1
import Mathlib.Tactic

/-!
# Fixed-witness full-ball sandwich for the frozen-graph tail budget

The retained-owner uniform full-ball endpoint can supply the middle inequality
of a three-term scalar sandwich.  This module records only that scalar
implication: its signature does not carry a packing certificate, cube bucket,
selected shading, or ball centre, and therefore does not by itself certify
that the three inequalities came from one geometric witness.  It also does
not select a new frozen graph, exact-card band, or fibre floor.

The two exposed comparisons are exactly the remaining seams:

* the desired frozen-graph tail numerator is paid into the full-ball left
  side;
* the full-ball right side, using the same local-ball witness, is paid into
  the fixed positive exact-card band.

No positivity, finiteness, cancellation, or stronger conclusion is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenUniformFullBallTailBudgetAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenQuantitativeLowerBucketFirstHitPaymentV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The literal left side of the quantitative lower-bucket tail budget. -/
def sameGraphQuantitativeLowerBucketTailLeft
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (displayed : ENNReal) : ENNReal :=
  quantitativeLowerBucketSelectionLoss tau *
    (displayed *
      (familyVolume (sourceActiveFineFamily P) *
        (((R.A.loss : ENNReal) *
          (P.index.coarse.card : ENNReal)) * R.graphLoss)))

/-- The volume of the fixed positive exact-card band occurring on the right
side of the quantitative lower-bucket tail budget. -/
def sameGraphPositiveExactCardBandVolume
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) : ENNReal :=
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real -> Real := fun _ => 0
  let positive := shadingAwareProjectedPhysical Z graph f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  volume (positive.multiplicityBand n n)

theorem sameGraphQuantitativeLowerBucketTailBudget_iff
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (fibreFloor displayed : ENNReal) :
    SameGraphQuantitativeLowerBucketTailBudget
        R n fibreFloor displayed <->
      sameGraphQuantitativeLowerBucketTailLeft R displayed <=
        fibreFloor * sameGraphPositiveExactCardBandVolume R n := by
  rfl

/-- The weakest scalar sandwich around any full-ball inequality.  Geometric
provenance is deliberately not claimed here; a stronger downstream wrapper
must bind these scalars to one explicit endpoint witness. -/
theorem sameGraphQuantitativeLowerBucketTailBudget_of_fullBallSandwich
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (fibreFloor displayed fullBallLeft fullBallRight : ENNReal)
    (hleft :
      sameGraphQuantitativeLowerBucketTailLeft R displayed <= fullBallLeft)
    (hfullBall : fullBallLeft <= fullBallRight)
    (hright : fullBallRight <=
      fibreFloor * sameGraphPositiveExactCardBandVolume R n) :
    SameGraphQuantitativeLowerBucketTailBudget
      R n fibreFloor displayed := by
  apply (sameGraphQuantitativeLowerBucketTailBudget_iff
    R n fibreFloor displayed).2
  exact hleft.trans (hfullBall.trans hright)

/-- Direct scalar shape of
`exists_retainedOwner_uniformFullBallPowerEndpoint`.  Its arguments match the
endpoint's final inequality, but the endpoint witness is not represented in
this theorem's type.  Consequently this is an algebraic adapter only, not a
proof of packing/graph witness alignment.

If `density` is chosen so that `hleft` is definitional, the sole new analytic
input is `hright`, the local-ball-to-positive-band payment for the same
frozen `R`, exact-card level `n`, and `fibreFloor`. -/
theorem sameGraphQuantitativeLowerBucketTailBudget_of_uniformFullBallScalarSandwich
    {iota : Type u} [Fintype iota]
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (fibreFloor displayed density localBallMass : ENNReal)
    (a b ballRadius : NNReal) (beta absorbExponent : Real)
    (hleft : sameGraphQuantitativeLowerBucketTailLeft R displayed <=
      density * ((a : ENNReal) * (b : ENNReal)) *
        volume (Metric.ball (0 : Space) (ballRadius : Real)))
    (hfullBall :
      density * ((a : ENNReal) * (b : ENNReal)) *
          volume (Metric.ball (0 : Space) (ballRadius : Real)) <=
        ((a : ENNReal) ^ (-absorbExponent) *
          (Fintype.card iota : ENNReal) ^ (1 - beta / 2)) * localBallMass)
    (hright :
      ((a : ENNReal) ^ (-absorbExponent) *
          (Fintype.card iota : ENNReal) ^ (1 - beta / 2)) * localBallMass <=
        fibreFloor * sameGraphPositiveExactCardBandVolume R n) :
    SameGraphQuantitativeLowerBucketTailBudget
      R n fibreFloor displayed := by
  exact sameGraphQuantitativeLowerBucketTailBudget_of_fullBallSandwich
    R n fibreFloor displayed
      (density * ((a : ENNReal) * (b : ENNReal)) *
        volume (Metric.ball (0 : Space) (ballRadius : Real)))
      (((a : ENNReal) ^ (-absorbExponent) *
        (Fintype.card iota : ENNReal) ^ (1 - beta / 2)) * localBallMass)
      hleft hfullBall hright

#print axioms sameGraphQuantitativeLowerBucketTailBudget_iff
#print axioms sameGraphQuantitativeLowerBucketTailBudget_of_fullBallSandwich
#print axioms
  sameGraphQuantitativeLowerBucketTailBudget_of_uniformFullBallScalarSandwich

end
end Family8CanonicalGraphFrozenUniformFullBallTailBudgetAdapterV1
