import Family8Grounding.Family8CanonicalGraphFrozenUniformFullBallSameWitnessAlignmentV1
import Family8Grounding.Family8ProjectedActiveShadingMassQuantitativeDyadicFibreBucketV2
import Mathlib.Tactic

/-!
# Canonical dyadic weighted-mass payment for the frozen-graph tail budget

The frozen graph fixes its graph shading, graph index set, zero projection,
and full projected/fibre windows.  This module evaluates the two-sided
dyadic-fibre weighted mass on exactly those objects.  On a measurable subset
of the same positive exact-card band, its geometric upper bound pays the
fixed uniform-full-ball witness alignment after cancelling the genuine
positive finite factor `2 * n`.

The only new scalar input is the forward payment from the literal local ball
to that canonical weighted mass.  No graph, exact-card level, window, final
fine shading, centre, or ball radius is reselected, and no finite-volume
assumption on the full fibre window is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenDyadicWeightedTailBudgetConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenQuantitativeLowerBucketFirstHitPaymentV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CanonicalGraphFrozenUniformFullBallSameWitnessAlignmentV1
open Family8CanonicalGraphFrozenUniformFullBallTailBudgetAdapterV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ProjectedActiveShadingMassQuantitativeDyadicFibreBucketV2
open Family8ShadingAwareProjectedPhysicalDyadicFibreBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

universe u v w

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The literal positive exact-card band already used on the right side of
the same-graph quantitative tail budget. -/
def sameGraphPositiveExactCardBand
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) : Set ProjectionSpace :=
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real -> Real := fun _ => 0
  let positive := shadingAwareProjectedPhysical Z graph f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  positive.multiplicityBand n n

/-- The two-sided fibre-bucket weighted mass on the exact graph, shading,
zero projection, and full windows fixed by `R`. -/
def sameGraphDyadicFibreBucketWeightedMass
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (level : ENNReal) (E : Set ProjectionSpace) : ENNReal :=
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real -> Real := fun _ => 0
  dyadicFibreBucketWeightedMass Z graph f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ level E

@[simp] theorem volume_sameGraphPositiveExactCardBand
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) :
    volume (sameGraphPositiveExactCardBand R n) =
      sameGraphPositiveExactCardBandVolume R n := rfl

/-- The canonical dyadic weighted upper bound closes the exact fixed-witness
alignment from one raw local-ball-to-weighted-mass payment.

The factor `2 * n` is forced by the two-sided bucket ceiling.  Its
cancellation is valid because the selected exact-card band supplies
`1 <= n`; no positivity or finiteness of the local-ball mass is required. -/
theorem sameGraphUniformFullBallWitnessAlignment_of_dyadicWeightedPayment
    {localIndex : Type v} [Fintype localIndex]
    {localFamily : ConvexFamily localIndex}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (hn : 1 <= n)
    (level coefficient : ENNReal) (hlevel : 0 < level)
    (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hEband : E <= sameGraphPositiveExactCardBand R n)
    (finalFine : Shading localFamily) (ballRadius : NNReal)
    (center : Space)
    (hWeightedPayment :
      (2 * (n : ENNReal)) *
          (coefficient *
            volume (finalFine.shadedUnion ∩
              Metric.ball center (ballRadius : Real))) <=
        sameGraphDyadicFibreBucketWeightedMass R level E) :
    SameGraphUniformFullBallWitnessAlignment
      R n level coefficient finalFine ballRadius center := by
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real -> Real := fun _ => 0
  have hUpper : sameGraphDyadicFibreBucketWeightedMass R level E <=
      (2 * level) * (n : ENNReal) * volume E := by
    simpa only [sameGraphDyadicFibreBucketWeightedMass, VS, graph, Z, f0]
      using
        dyadicFibreBucketWeightedMass_le_two_mul_level_mul_originalCard_mul_volume
          Z graph f0 measurable_const Set.univ MeasurableSet.univ
            Set.univ MeasurableSet.univ level hlevel n E hE (by
              simpa only [sameGraphPositiveExactCardBand, VS, graph, Z, f0]
                using hEband)
  have hVolume : volume E <= sameGraphPositiveExactCardBandVolume R n := by
    rw [← volume_sameGraphPositiveExactCardBand R n]
    exact measure_mono hEband
  have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnZero : (n : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hnPos)
  have hFactorZero : 2 * (n : ENNReal) ≠ 0 :=
    mul_ne_zero (by norm_num) hnZero
  have hFactorTop : 2 * (n : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top n)
  have hScaled :
      (2 * (n : ENNReal)) *
          (coefficient *
            volume (finalFine.shadedUnion ∩
              Metric.ball center (ballRadius : Real))) <=
        (2 * (n : ENNReal)) *
          (level * sameGraphPositiveExactCardBandVolume R n) := by
    calc
      (2 * (n : ENNReal)) *
            (coefficient *
              volume (finalFine.shadedUnion ∩
                Metric.ball center (ballRadius : Real))) <=
          sameGraphDyadicFibreBucketWeightedMass R level E :=
        hWeightedPayment
      _ <= (2 * level) * (n : ENNReal) * volume E := hUpper
      _ = (2 * (n : ENNReal)) * (level * volume E) := by ac_rfl
      _ <= (2 * (n : ENNReal)) *
          (level * sameGraphPositiveExactCardBandVolume R n) := by
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hVolume)
  refine { localBall_payment := ?_ }
  exact (ENNReal.mul_le_mul_iff_right hFactorZero hFactorTop).mp hScaled

/-- Final same-`R` TailBudget connector.  The endpoint full-ball inequality
and the dyadic weighted payment mention the same `finalFine`, centre, and
ball radius.  The graph shading, graph window, exact-card band, and fibre
bucket are definitionally fixed by `R`; none is selected by this theorem. -/
theorem sameGraphQuantitativeLowerBucketTailBudget_of_fixedUniformFullBallPayload_and_dyadicWeightedPayment
    {endpointIndex : Type v} [Fintype endpointIndex]
    {localFineIndex : Type w} [Fintype localFineIndex]
    {localFineFamily : ConvexFamily localFineIndex}
    {localCoarseIndex : Type w} [Fintype localCoarseIndex]
    {localCoarseFamily : ConvexFamily localCoarseIndex}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (n : Nat) (hn : 1 <= n)
    (level displayed density : ENNReal) (hlevel : 0 < level)
    (a b ballRadius : NNReal) (beta absorbExponent : Real)
    (E : Set ProjectionSpace) (hE : MeasurableSet E)
    (hEband : E <= sameGraphPositiveExactCardBand R n)
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
    (hWeightedPayment :
      (2 * (n : ENNReal)) *
          (((a : ENNReal) ^ (-absorbExponent) *
              (Fintype.card endpointIndex : ENNReal) ^ (1 - beta / 2)) *
            volume (finalFine.shadedUnion ∩
              Metric.ball center (ballRadius : Real))) <=
        sameGraphDyadicFibreBucketWeightedMass R level E) :
    SameGraphQuantitativeLowerBucketTailBudget
      R n level displayed := by
  have hAlignment : SameGraphUniformFullBallWitnessAlignment
      R n level
        ((a : ENNReal) ^ (-absorbExponent) *
          (Fintype.card endpointIndex : ENNReal) ^ (1 - beta / 2))
        finalFine ballRadius center :=
    sameGraphUniformFullBallWitnessAlignment_of_dyadicWeightedPayment
      R n hn level
        ((a : ENNReal) ^ (-absorbExponent) *
          (Fintype.card endpointIndex : ENNReal) ^ (1 - beta / 2))
        hlevel E hE hEband finalFine ballRadius center
        hWeightedPayment
  exact
    sameGraphQuantitativeLowerBucketTailBudget_of_fixedUniformFullBallPayload
      (endpointIndex := endpointIndex) R n level displayed density
        a b ballRadius beta absorbExponent finalFine finalCoarse center
          hcenter hleft hfullBall hAlignment

#print axioms volume_sameGraphPositiveExactCardBand
#print axioms
  sameGraphUniformFullBallWitnessAlignment_of_dyadicWeightedPayment
#print axioms
  sameGraphQuantitativeLowerBucketTailBudget_of_fixedUniformFullBallPayload_and_dyadicWeightedPayment

end
end Family8CanonicalGraphFrozenDyadicWeightedTailBudgetConnectorV1
