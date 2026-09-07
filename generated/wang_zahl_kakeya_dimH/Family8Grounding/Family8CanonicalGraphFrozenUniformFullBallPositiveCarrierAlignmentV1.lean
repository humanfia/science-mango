import Family8Grounding.Family8CanonicalGraphFrozenUniformFullBallSameWitnessAlignmentV1
import Family8Grounding.Family8ExactAssemblySameDataFiberBridgeV1
import Family8Grounding.Family8PositiveCarrierShadingRestrictionLocalVolumeV1

/-!
# Positive-carrier transport for one fixed full-ball witness

The retained-owner endpoint and the positive-carrier compaction can present
the same local fine shading with different finite index types.  Removing the
zero-volume carriers does not change its volume in the fixed endpoint ball.
This module transports the full-ball payload and the same-graph alignment
without changing the centre, radius, frozen graph, exact-card level, fibre
floor, or coefficient.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenUniformFullBallPositiveCarrierAlignmentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CanonicalGraphFrozenUniformFullBallSameWitnessAlignmentV1
open Family8CanonicalGraphFrozenUniformFullBallTailBudgetAdapterV1
open Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8PositiveCarrierShadingRestrictionLocalVolumeV1
open Family8PositiveCarrierShadingRestrictionV4
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u v

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

variable {localIndex : Type v} [Fintype localIndex]
  {localFamily : ConvexFamily localIndex}

/-- Removing zero-volume carriers preserves the volume in the literal fixed
endpoint ball.  This is the ball-specialized form of the general measurable
window identity. -/
@[simp] theorem positiveCarrierShading_localBall_volume
    (rawFine : Shading localFamily) (center : Space) (ballRadius : NNReal) :
    volume ((positiveCarrierShading rawFine).shadedUnion ∩
        Metric.ball center (ballRadius : Real)) =
      volume (rawFine.shadedUnion ∩
        Metric.ball center (ballRadius : Real)) := by
  exact positiveCarrierShading_shadedUnion_inter_volume rawFine
    (Metric.ball center (ballRadius : Real)) measurableSet_ball

/-- The physical union in one fixed endpoint ball is automatically paid by
the multiplicity-counted mass of the restriction of the very same shading to
that ball.  This is the first, witness-preserving step of a selection-first
local ledger. -/
theorem localBall_volume_le_fixedBallRestrictedShadingMass
    (finalFine : Shading localFamily) (center : Space)
    (ballRadius : NNReal) :
    volume (finalFine.shadedUnion ∩
        Metric.ball center (ballRadius : Real)) ≤
      (finalFine.restrictSet
        (Metric.ball center (ballRadius : Real))
        measurableSet_ball).shadingMass := by
  rw [← Shading.restrictSet_shadedUnion finalFine
    (Metric.ball center (ballRadius : Real)) measurableSet_ball]
  exact volume_shadedUnion_le_shadingMass _

/-- The fixed-witness alignment is invariant under positive-carrier
compaction.  The two sides may have different index types, but all geometric
witnesses and every scalar remain literally unchanged. -/
theorem sameGraphUniformFullBallWitnessAlignment_positiveCarrier_iff
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (bandLevel : Nat) (fibreFloor coefficient : ENNReal)
    (rawFine : Shading localFamily) (ballRadius : NNReal)
    (center : Space) :
    SameGraphUniformFullBallWitnessAlignment R bandLevel fibreFloor
        coefficient (positiveCarrierShading rawFine) ballRadius center ↔
      SameGraphUniformFullBallWitnessAlignment R bandLevel fibreFloor
        coefficient rawFine ballRadius center := by
  constructor
  · intro h
    refine { localBall_payment := ?_ }
    simpa only [positiveCarrierShading_localBall_volume] using
      h.localBall_payment
  · intro h
    refine { localBall_payment := ?_ }
    simpa only [positiveCarrierShading_localBall_volume] using
      h.localBall_payment

/-- Factor the fixed local-ball alignment through any caller-supplied scalar
cap.  This is the weakest interface matching the endpoint's automatic upper
bound on its selected ball: the geometric endpoint proves `hLocalCap`, while
the remaining same-object scalar work is exposed solely as `hCapPayment`.
No graph, band, fine shading, centre, or radius is selected here. -/
theorem sameGraphUniformFullBallWitnessAlignment_of_localBallCap
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (bandLevel : Nat) (fibreFloor coefficient cap : ENNReal)
    (finalFine : Shading localFamily) (ballRadius : NNReal)
    (center : Space)
    (hLocalCap :
      volume (finalFine.shadedUnion ∩
        Metric.ball center (ballRadius : Real)) ≤ cap)
    (hCapPayment :
      coefficient * cap ≤
        fibreFloor * sameGraphPositiveExactCardBandVolume R bandLevel) :
    SameGraphUniformFullBallWitnessAlignment R bandLevel fibreFloor
      coefficient finalFine ballRadius center := by
  refine { localBall_payment := ?_ }
  exact (mul_le_mul' le_rfl hLocalCap).trans hCapPayment

/-- A fixed-ball restricted shading-mass payment implies the exact alignment.
Unlike a direct union payment, its left side is a finite sum of the unchanged
carrier restrictions and is therefore the natural input for Fubini or an
incidence ledger. -/
theorem sameGraphUniformFullBallWitnessAlignment_of_fixedBallRestrictedShadingMassPayment
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (bandLevel : Nat) (fibreFloor coefficient : ENNReal)
    (finalFine : Shading localFamily) (ballRadius : NNReal)
    (center : Space)
    (hRestrictedPayment :
      coefficient *
          (finalFine.restrictSet
            (Metric.ball center (ballRadius : Real))
            measurableSet_ball).shadingMass ≤
        fibreFloor * sameGraphPositiveExactCardBandVolume R bandLevel) :
    SameGraphUniformFullBallWitnessAlignment R bandLevel fibreFloor
      coefficient finalFine ballRadius center := by
  apply sameGraphUniformFullBallWitnessAlignment_of_localBallCap
    R bandLevel fibreFloor coefficient
      ((finalFine.restrictSet
        (Metric.ball center (ballRadius : Real))
        measurableSet_ball).shadingMass)
      finalFine ballRadius center
  · exact localBall_volume_le_fixedBallRestrictedShadingMass
      finalFine center ballRadius
  · exact hRestrictedPayment

/-- The same cap factorization when the endpoint shading has first been
compacted to its positive carriers.  The raw local-ball cap is reused exactly
at the same centre and radius. -/
theorem sameGraphUniformFullBallWitnessAlignment_positiveCarrier_of_rawLocalBallCap
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (bandLevel : Nat) (fibreFloor coefficient cap : ENNReal)
    (rawFine : Shading localFamily) (ballRadius : NNReal)
    (center : Space)
    (hLocalCap :
      volume (rawFine.shadedUnion ∩
        Metric.ball center (ballRadius : Real)) ≤ cap)
    (hCapPayment :
      coefficient * cap ≤
        fibreFloor * sameGraphPositiveExactCardBandVolume R bandLevel) :
    SameGraphUniformFullBallWitnessAlignment R bandLevel fibreFloor
      coefficient (positiveCarrierShading rawFine) ballRadius center := by
  apply sameGraphUniformFullBallWitnessAlignment_of_localBallCap
    R bandLevel fibreFloor coefficient cap
      (positiveCarrierShading rawFine) ballRadius center
  · simpa only [positiveCarrierShading_localBall_volume] using hLocalCap
  · exact hCapPayment

/-- A universal fixed-radius full-ball payload is likewise invariant under
positive-carrier compaction of the same fine shading. -/
theorem uniformFullBallPayload_positiveCarrier_iff
    {coarseIndex : Type u} [Fintype coarseIndex]
    {coarseFamily : ConvexFamily coarseIndex}
    (rawFine : Shading localFamily) (finalCoarse : Shading coarseFamily)
    (left coefficient : ENNReal) (ballRadius : NNReal) :
    (∀ x, x ∈ finalCoarse.shadedUnion →
        left ≤ coefficient *
          volume ((positiveCarrierShading rawFine).shadedUnion ∩
            Metric.ball x (ballRadius : Real))) ↔
      (∀ x, x ∈ finalCoarse.shadedUnion →
        left ≤ coefficient *
          volume (rawFine.shadedUnion ∩
            Metric.ball x (ballRadius : Real))) := by
  constructor <;> intro h x hx
  · simpa only [positiveCarrierShading_localBall_volume] using h x hx
  · simpa only [positiveCarrierShading_localBall_volume] using h x hx

#print axioms positiveCarrierShading_localBall_volume
#print axioms localBall_volume_le_fixedBallRestrictedShadingMass
#print axioms sameGraphUniformFullBallWitnessAlignment_positiveCarrier_iff
#print axioms sameGraphUniformFullBallWitnessAlignment_of_localBallCap
#print axioms
  sameGraphUniformFullBallWitnessAlignment_of_fixedBallRestrictedShadingMassPayment
#print axioms
  sameGraphUniformFullBallWitnessAlignment_positiveCarrier_of_rawLocalBallCap
#print axioms uniformFullBallPayload_positiveCarrier_iff

end

end Family8CanonicalGraphFrozenUniformFullBallPositiveCarrierAlignmentV1
